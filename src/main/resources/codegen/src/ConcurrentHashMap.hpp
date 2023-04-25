//
// Created by Aaron Bembenek on 4/25/23.
//

#pragma once

#include <oneapi/tbb/concurrent_unordered_map.h>

namespace flg {

template<typename Key, typename Value, typename Hash = std::hash<Key>, typename Equals = std::equal_to<Key>>
using ConcurrentHashMap = tbb::concurrent_unordered_map<Key, Value, Hash, Equals>;

}