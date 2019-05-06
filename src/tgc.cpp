/* $Id$ */

/*
 * This file is part of OpenTTD.
 * OpenTTD is free software; you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, version 2.
 * OpenTTD is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details. You should have received a copy of the GNU General Public License along with OpenTTD. If not, see <http://www.gnu.org/licenses/>.
 */

/** @file tgc.cpp OTTD Continental Landscape Generator */

#include "stdafx.h"
#include <math.h>
#include "clear_map.h"
#include "void_map.h"
#include "genworld.h"
#include "core/random_func.hpp"
#include "landscape_type.h"
#include <queue>

#include "safeguards.h"

// Used to allow storage of points in a set, specifically the Continents type.
struct PointComparator {
	bool operator() (const Point &a, const Point &b) const
	{
		if (a.x == b.x) {
			return a.y < b.y;
		} else {
			return a.x < b.x;
		}
	}
};

typedef std::set<Point, PointComparator> PointSet;

struct Continent {
	// Starting tile for this continent.
	Point seed;
	// True if land, false if ocean.
	bool is_land;
	// Magnitude of force of continental drift
	double magnitude;
	double angle;
};

typedef std::vector<Continent> Continents;

/** Height map - allocated array of heights (MapSizeX() + 1) x (MapSizeY() + 1) */
struct HeightMap
{
	// height at each coordinate
	int *h;
	// continent at each coordinate
	int *c;
	int dim_x;
	int total_size;
	int size_x;
	int size_y;

	inline int &height(uint x, uint y)
	{
		return h[x + y * dim_x];
	}

	inline int &continent(uint x, uint y)
	{
		return c[x + y * dim_x];
	}
};

/** Global data structure instances */
static HeightMap _height_map = {NULL, NULL, 0, 0, 0, 0};
static Continents _continents(0);


/**
 * Check if a point is within the map boundaries.
 */
static inline bool IsValidPoint(Point p)
{
	return p.x >= 0 && p.x <= _height_map.size_x && p.y >= 0 && p.y <= _height_map.size_y;
}

static inline double distance_weight(double a_x, double a_y, double b_x, double b_y)
{
	// Each *_diff takes on a value between 0 and 1
	double x_diff = (b_x - a_x) / _height_map.size_x;
	double y_diff = (b_y - a_y) / _height_map.size_y;
	// Weight is a value between 0 and 1
	double weight = (x_diff * x_diff + y_diff * y_diff) / 2.0;
	// Invert weight so greater distances have lower weights
	return 1.0 - weight;
}

/**
 * Allocate array of (MapSizeX()+1)*(MapSizeY()+1) heights and init the _height_map structure members
 * @return true on success
 */
static inline bool AllocHeightMap()
{
	_height_map.size_x = MapSizeX();
	_height_map.size_y = MapSizeY();

	/* Allocate memory block for height map row pointers */
	_height_map.total_size = (_height_map.size_x + 1) * (_height_map.size_y + 1);
	_height_map.dim_x = _height_map.size_x + 1;
	_height_map.h = CallocT<int>(_height_map.total_size);
	_height_map.c = CallocT<int>(_height_map.total_size);

	/* Iterate through height map and initialise values. */
	for (int i = 0; i < _height_map.total_size; i++) {
		_height_map.h[i] = 0;
		_height_map.c[i] = -1;
	}

	// A 64x64 map has 4 continents. This scales up such that larger maps have
	// larger continents.
	int num_continents = _height_map.size_x * _height_map.size_y / 12000 + 4;
	_continents = Continents(num_continents);

	return true;
}

/** Free height map */
static inline void FreeHeightMap()
{
	free(_height_map.h);
	_height_map.h = NULL;
	free(_height_map.c);
	_height_map.c = NULL;

	_continents = Continents(0);
}


/** A small helper function to initialize the terrain */
static void TgenSetTileHeight(TileIndex tile, int height)
{
	SetTileHeight(tile, height);

	/* Only clear the tiles within the map area. */
	if (IsInnerTile(tile)) {
		MakeClear(tile, CLEAR_GRASS, 3);
	}
}

/**
 * Runs the given function for each point immediately adjacent to the given
 * point.
 */
static void ForAdjacent(Point point, std::function<void(Point)> run)
{
	const Point offsets[4] = {Point{-1, 0}, Point{1, 0}, Point{0, -1}, Point{0, 1}};
	for (int i = 0; i < 4; i++) {
		Point new_point = Point{point.x + offsets[i].x, point.y + offsets[i].y};
		if (IsValidPoint(new_point)) {
			run(new_point);
		}
	}
}

/**
 * Runs the given function for each point located in a box of the given radius
 * around the given point.
 */
static void ForAdjacentBox(Point point, int radius, std::function<void(Point, int, int)> run)
{
	for (int i = -radius; i <= radius; i++) {
		for (int j = -radius; j <= radius; j++) {
			Point adj = Point{point.x + j, point.y + i};
			if (IsValidPoint(adj)) {
				run(adj, i, j);
			}
		}
	}
}

/**
 * Selects a random point from the given source that isn't already assigned a
 * continent. Returns Point{-1, -1} if no points are available.
 */
static Point GetRandomFreePoint(std::vector<Point> *source)
{
	while (!source->empty()) {
		int index = RandomRange(source->size()) % source->size();
		Point new_point = (*source)[index];
		source->erase(source->begin() + index);
		if (_height_map.continent(new_point.x, new_point.y) < 0) {
			return new_point;
		}
	}

	return Point{-1, -1};
}

// Randomly pick continents and assign each one a single starting tile.
static void SeedContinents()
{
	assert(_height_map.c != NULL);

	// Calculate the percentage of continents that should be water
	int sea_level_setting = _settings_game.difficulty.quantity_sea_lakes;
	double water_percent = sea_level_setting == CUSTOM_SEA_LEVEL_NUMBER_DIFFICULTY ? _settings_game.game_creation.custom_sea_level / 100.0 : (sea_level_setting + 1) / 5.0;

	// Calculate magnitude of land drift based on map size so larger maps
	// have higher peaks.
	// size is between 6 and 12, inclusive
	double size = log2(min(_height_map.size_x, _height_map.size_y));
	double n_size = (size - 6.0) / 6.0;
	double land_magnitude = min(n_size * 3.0 + 2.0, 3.5);
	// Scale drift (and subsequently mountain height) based on selected terrain type
	land_magnitude *= (_settings_game.difficulty.terrain_type + 1) / 4.0;

	// Pick a seed location for each continent.
	int num_continents = _continents.size();
	PointSet used_points;
	for (int i = 0; i < num_continents; i++) {
		Point p;
		do {
			int x = RandomRange(_height_map.size_x);
			int y = RandomRange(_height_map.size_y);
			p = {x, y};
		} while (used_points.find(p) != used_points.end());

		_continents[i].seed = p;
		_height_map.continent(p.x, p.y) = i;
		_continents[i].is_land = i > water_percent * num_continents;
		_continents[i].magnitude = _continents[i].is_land ? land_magnitude : 0.8;
		_continents[i].angle = RandomRange(8) % 8 * M_PI / 4.0;
		used_points.insert(p);
	}
}

// Randomly expand each continent until every tile has a continent.
static void ExpandContinents()
{
	assert(_height_map.c != NULL);

	int variety = _settings_game.game_creation.variety + 1;
	int num_continents = _continents.size();
	std::vector<std::vector<Point>> queues(num_continents);
	std::vector<int> active_continents(0);
	for (int i = 0; i < num_continents; i++) {
	int continent_weight = RandomRange(variety) % variety + 1;
	for (int j = 0; j < continent_weight; j++) {
		active_continents.push_back(i);
	}

		Point p = _continents[i].seed;
		auto add_to_q = [&](Point p) {
			if (_height_map.continent(p.x, p.y) < 0) {
				queues[i].push_back(p);
			}
		};
		ForAdjacent(p, add_to_q);
	}

	// Randomly expand each continent by one coordinate until we've used up
	// the entire map.
	while (!active_continents.empty()) {
		int index_index = RandomRange(active_continents.size()) % active_continents.size();
		int continent_index = active_continents[index_index];
		std::vector<Point> *q = &queues[continent_index];

		Point new_point = GetRandomFreePoint(q);
		// If queue is empty, this continent is done expanding.
		if (q->empty()) {
			active_continents.erase(active_continents.begin() + index_index);
			continue;
		}

		_height_map.continent(new_point.x, new_point.y) = continent_index;
		auto add_to_q = [&](Point p) {
			if (_height_map.continent(p.x, p.y) < 0) {
				q->push_back(p);
			}
		};
		ForAdjacent(new_point, add_to_q);
	}
}

static bool AllTilesAssigned()
{
	for (int y = 0; y <= _height_map.size_y; y++) {
		for (int x = 0; x <= _height_map.size_x; x++) {
			if (_height_map.continent(x, y) < 0) {
				return false;
			}
		}
	}
	return true;
}

// Give each land tile a height of 1 and each ocean tile a height of 0.
static void SetBaselineHeights()
{
	assert(_height_map.h != NULL);
	assert(_height_map.c != NULL);

	for (int i = 0; i < _height_map.total_size; i++) {
		int c_i = _height_map.c[i];
		if (c_i >= 0) {
			_height_map.h[i] = _continents[c_i].is_land ? 1 : 0;
		} else {
			_height_map.h[i] = 0;
		}
	}
}

// Creates mountain peaks where continents collide.
static void CreatePeaks()
{
	assert(_height_map.h != NULL);
	assert(_height_map.c != NULL);

	for (int y = 0; y <= _height_map.size_y; y++) {
		for (int x = 0; x <= _height_map.size_x; x++) {
			int continent_i = _height_map.continent(x, y);
			Continent *continent = &_continents[continent_i];
			double peak = 0;

			auto smash = [&](Point adj, int i, int j) {
				int adj_continent_i = _height_map.continent(adj.x, adj.y);
				if (continent_i == adj_continent_i) return;

				Continent *adj_continent = &_continents[adj_continent_i];
				double angle = atan2(i, j);

				// Calculate different weights based on different factors

				// This is our primary factor: the angle of drift at this point.
				// An angle towards the center creates a mountain, and away from
				// the center creates a lake.
				double angle_w = sin((angle - continent->angle) / 2.0);
				double adj_angle_w = sin((-angle - adj_continent->angle) / 2.0);

				double dist_w = 1.0;
				if (continent->is_land && !adj_continent->is_land) {
					// Try to skew mountains away from coasts
					double dist_i_w = abs(i) / 3.0;
					double dist_j_w = abs(j) / 3.0;
					dist_w = dist_i_w * dist_j_w;
				} else {
					// Forces closer to the center are weighted more heavily.
					double dist_i_w = (4 - abs(i)) / 4.0;
					double dist_j_w = (4 - abs(j)) / 4.0;
					dist_w = dist_i_w * dist_j_w;
				}

				// Tiles closer to the center point have more force than those
				// further away.
				double m = distance_weight(x, y, continent->seed.x, continent->seed.y);
				double adj_m = distance_weight(adj.x, adj.y, adj_continent->seed.x, adj_continent->seed.y);

				peak += angle_w * continent->magnitude * dist_w * m * 3;
				peak += adj_angle_w * adj_continent->magnitude * dist_w * adj_m * 3;
			};
			ForAdjacentBox(Point{x, y}, 2, smash);

			_height_map.height(x, y) += (int)peak;
		}
	}
}

// Adds slopes to the sides of mountain peaks.
static void FillMountains()
{
	assert(_height_map.h != NULL);
	assert(_height_map.c != NULL);

	std::queue<Point> to_fix;
	auto add_to_q = [&](Point p) { to_fix.push(p); };

	// Gather list of tiles adjacent to peaks (tiles with height > 1)
	for (int y = 0; y <= _height_map.size_y; y++) {
		for (int x = 0; x <= _height_map.size_x; x++) {
			if (_height_map.height(x, y) > 1) {
				ForAdjacent(Point{x, y}, add_to_q);
			}
		}
	}

	// For each tile, make sure adjacent tiles are at most one level above or
	// below
	while (!to_fix.empty()) {
		Point p = to_fix.front();
		to_fix.pop();

		// Calculate the maximum adjacent height
		int max_adj = 0;
		auto calc_max = [&](Point np) {
			int h = _height_map.height(np.x, np.y);
			if (h > max_adj) {
				max_adj = h;
			}
		};
		ForAdjacent(p, calc_max);

		// If height of this point is already valid, do nothing
		if (_height_map.height(p.x, p.y) >= max_adj - 1) {
			continue;
		}

		int c_i = _height_map.continent(p.x, p.y);
		Continent *c = &_continents[c_i];
		// Increase spread (the width of mountains) at lower elevations
		int spread = c->is_land ? 2 : 4;
		if (c->is_land && max_adj < 7) {
			spread += 7 - max_adj;
		}
		_height_map.height(p.x, p.y) = Chance16(spread, 10) ? max_adj : max_adj - 1;
		ForAdjacent(p, add_to_q);
	}
}

// Clamp all heights between 0 and the maximum height.
static void ClampHeights(bool symmetric)
{
	assert(_height_map.h != NULL);

	int max_height = _settings_game.construction.max_heightlevel;
	int min_height = symmetric ? -max_height : 0;
	for (int i = 0; i < _height_map.total_size; i++) {
		_height_map.h[i] = Clamp(_height_map.h[i], min_height, max_height);
	}
}

// Smooth the map by applying a pyramidal blur filter.
static void SmoothHoles()
{
	assert(_height_map.h != NULL);

	std::vector<int> new_heights(_height_map.total_size);

	for (int y = 0; y <= _height_map.size_y; y++) {
		for (int x = 0; x <= _height_map.size_x; x++) {
			Point p = Point{x, y};
			int h = _height_map.height(x, y);

			if (h <= 0) continue;

			int total_weight = 0;
			int total_value = 0;
			auto sum = [&](Point np, int i, int j) {
				int nh = _height_map.height(np.x, np.y);
				int w = 2 - (abs(i) + abs(j));
				total_weight += w;
				total_value += w * nh;
			};
			ForAdjacentBox(p, 3, sum);
			sum(p, 0, 0);

			int new_height = round(total_value / (double) total_weight);
			new_heights[x + y * _height_map.dim_x] = new_height;
		}
	}

	for (int i = 0; i < _height_map.total_size; i++) {
		_height_map.h[i] = new_heights[i];
	}
}

/**
 * Lowers the given tile to the given height and corrects surrounding tiles so
 * map is valid. Only used for lowering, not raising land.
 */
static void LowerLand(int x, int y, int new_height)
{
	assert(new_height >= 0);
	int current_height = _height_map.height(x, y);
	assert(new_height <= current_height);

	if (new_height == current_height) return;

	_height_map.height(x, y) = new_height;
	auto lower = [&](Point p) {
		LowerLand(p.x, p.y, min(_height_map.height(p.x, p.y), new_height + 1));
	};
	ForAdjacent(Point{x, y}, lower);
}

static void SetBorders()
{
	byte water_borders = _settings_game.construction.freeform_edges ? _settings_game.game_creation.water_borders : 0xF;
	if (water_borders == BORDERS_RANDOM) water_borders = GB(Random(), 0, 4);

	if (HasBit(water_borders, BORDER_NE)) {
		for (int y = 0; y <= _height_map.size_y; y++) {
			int max_x = RandomRange(4) + 4;
			for (int x = 0; x < max_x; x++) {
				LowerLand(x, y, 0);
			}
		}
	}

	if (HasBit(water_borders, BORDER_SW)) {
		for (int y = 0; y <= _height_map.size_y; y++) {
			int max_x = RandomRange(4) + 4;
			for (int x = _height_map.size_x; x >= _height_map.size_x - max_x; x--) {
				LowerLand(x, y, 0);
			}
		}
	}

	if (HasBit(water_borders, BORDER_NW)) {
		for (int x = 0; x <= _height_map.size_x; x++) {
			int max_y = RandomRange(4) + 4;
			for (int y = 0; y < max_y; y++) {
				LowerLand(x, y, 0);
			}
		}
	}

	if (HasBit(water_borders, BORDER_SE)) {
		for (int x = 0; x <= _height_map.size_x; x++) {
			int max_y = RandomRange(4) + 4;
			for (int y = _height_map.size_y; y >= _height_map.size_y - max_y; y--) {
				LowerLand(x, y, 0);
			}
		}
	}
}

/**
 * The continental land generator.
 */
void GenerateTerrainContinents()
{
	if (!AllocHeightMap()) return;
	GenerateWorldSetAbortCallback(FreeHeightMap);

	SetRandomSeed(_settings_game.game_creation.generation_seed);
	SeedContinents();

	IncreaseGeneratingWorldProgress(GWP_LANDSCAPE);

	ExpandContinents();
	assert(AllTilesAssigned());

	SetBaselineHeights();

	CreatePeaks();
	ClampHeights(true);
	FillMountains();
	ClampHeights(false);

	int smoothness = 3 - _settings_game.game_creation.tgen_smoothness;
	for (int i = 0; i < smoothness; i++) {
		SmoothHoles();
	}

	SetBorders();

	// I'm not sure what this does but without it the game crashes.
	// Taken from tgp.cpp where it says:
	// "First make sure the tiles at the north border are void tiles if needed."
	if (_settings_game.construction.freeform_edges) {
		for (uint x = 0; x < MapSizeX(); x++) MakeVoid(TileXY(x, 0));
		for (uint y = 0; y < MapSizeY(); y++) MakeVoid(TileXY(0, y));
	}

	/* Transfer height map into OTTD map */
	for (int y = 0; y < _height_map.size_y; y++) {
		for (int x = 0; x < _height_map.size_x; x++) {
			int h = _height_map.height(x, y);
			TgenSetTileHeight(TileXY(x, y), Clamp(h, 0, _settings_game.construction.max_heightlevel));
		}
	}

	IncreaseGeneratingWorldProgress(GWP_LANDSCAPE);

	FreeHeightMap();
	GenerateWorldSetAbortCallback(NULL);
}
