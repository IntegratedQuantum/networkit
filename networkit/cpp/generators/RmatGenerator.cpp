/*
 * RmatGenerator.cpp
 *
 *  Created on: 18.03.2014
 *      Author: Henning, cls
 *
 * Uses the algorithm described by Hübschle-Schneider and Sanders in
 * "Linear Work Generation of R-MAT Graphs" https://arxiv.org/abs/1905.03525
 */

#include <networkit/auxiliary/Log.hpp>
#include <networkit/auxiliary/NumericTools.hpp>
#include <networkit/auxiliary/Random.hpp>
#include <networkit/generators/RmatGenerator.hpp>

namespace NetworKit {

RmatGenerator::RmatGenerator(count scale, count edgeFactor, double a, double b, double c, double d,
                             bool weighted, count reduceNodes)
    : scale(scale), edgeFactor(edgeFactor), a(a), b(b), c(c), weighted(weighted),
      reduceNodes(reduceNodes) {
    if (scale > 63)
        throw std::runtime_error("Cannot generate more than 2^63 nodes");
    double sum = a + b + c + d;
    INFO("sum of probabilities: ", sum);
    if (!Aux::NumericTools::equal(sum, 1.0, 0.0001))
        throw std::runtime_error("Probabilities in Rmat have to sum to 1.");
    defaultEdgeWeight = 1.0;
}

struct Entry {
    uint32_t i;
    uint32_t j;
    uint32_t numberOfBits;
    double probability;
};

struct AliasTable {
    std::vector<std::pair<uint32_t, uint32_t>> bits;
    std::vector<uint8_t> numberOfBits;
    std::vector<uint32_t> coinFlipProbability;
    std::vector<uint32_t> coinFlipReplacement;
    uint32_t mask;
    std::pair<uint32_t, uint32_t> curBits{0, 0};
    uint32_t remainingBits = 0;

    void sample(std::mt19937_64 &urng) {
        std::uniform_int_distribution<uint64_t> dist;
        uint64_t randomNumber = dist(urng);
        uint32_t index = randomNumber & mask;
        uint32_t coinFlip = randomNumber >> 32;
        if (coinFlip <= coinFlipProbability[index]) {
            index = coinFlipReplacement[index];
        }
        curBits = bits[index];
        remainingBits = numberOfBits[index];
    }

    std::pair<node, node> sampleEdge(std::mt19937_64 &urng, uint8_t bits) {
        std::pair<node, node> result{0, 0};
        while (true) {
            if (remainingBits >= bits) {
                remainingBits -= bits;
                result.first = result.first << bits | curBits.first >> remainingBits;
                result.second = result.second << bits | curBits.second >> remainingBits;
                curBits.first &= (1 << remainingBits) - 1;
                curBits.second &= (1 << remainingBits) - 1;
                return result;
            }
            result.first = result.first << remainingBits | curBits.first;
            result.second = result.second << remainingBits | curBits.second;
            bits -= remainingBits;

            sample(urng);
        }
    }
};

bool priorityQueueCompare(const Entry &a, const Entry &b) {
    return a.probability < b.probability && (a.numberOfBits < 32 || b.numberOfBits == 32);
}

// std::priority_queue doesn't support iterating over its elements.
struct PriorityQueue {
    std::vector<Entry> &internal;

    PriorityQueue(std::vector<Entry> &vec) : internal(vec) {}

    void push(Entry &&entry) {
        internal.push_back(entry);
        std::push_heap(internal.begin(), internal.end(), priorityQueueCompare);
    }

    Entry pop() {
        std::pop_heap(internal.begin(), internal.end(), priorityQueueCompare);
        Entry result = internal.back();
        internal.pop_back();
        return result;
    }
};

void generateEntries(std::vector<Entry> &entryList, count size, double a, double b, double c,
                     double d) {
    entryList.reserve(size);
    PriorityQueue priorityQueue(entryList);
    priorityQueue.push(Entry{0, 0, 1, a});
    priorityQueue.push(Entry{0, 1, 1, b});
    priorityQueue.push(Entry{1, 0, 1, c});
    priorityQueue.push(Entry{1, 1, 1, d});
    while (entryList.size() <= size - 3) {
        // Take the entry with the highest probability and split it up.
        // This increases the average number of bits compared to a uniform distribution.
        Entry old = priorityQueue.pop();
        priorityQueue.push(
            Entry{old.i << 1 | 0, old.j << 1 | 0, old.numberOfBits + 1, a * old.probability});
        priorityQueue.push(
            Entry{old.i << 1 | 0, old.j << 1 | 1, old.numberOfBits + 1, b * old.probability});
        priorityQueue.push(
            Entry{old.i << 1 | 1, old.j << 1 | 0, old.numberOfBits + 1, c * old.probability});
        priorityQueue.push(
            Entry{old.i << 1 | 1, old.j << 1 | 1, old.numberOfBits + 1, d * old.probability});
    }
}

void generateTable(AliasTable &table, count size, double a, double b, double c, double d) {
    assert(size & size - 1 == 0); // The size must be a power of two.
    std::vector<Entry> entryList;
    generateEntries(entryList, size, a, b, c, d);
    while (entryList.size() < size) { // Fill the remaining entries with 0-probability entries.
        entryList.push_back(Entry{0, 0, 0, 0});
    }

    // Construct the alias table:
    table.mask = size - 1;
    table.bits.resize(size);
    table.numberOfBits.resize(size);
    table.coinFlipProbability.resize(size);
    table.coinFlipReplacement.resize(size);
    for (int i = 0; i < size; i++) {
        table.bits[i] = std::make_pair(entryList[i].i, entryList[i].j);
        table.numberOfBits[i] = entryList[i].numberOfBits;
        table.coinFlipProbability[i] = 0;
        table.coinFlipReplacement[i] = 0;
    }
    double baseProbability = 1.0 / (double)size;
    int lastOverfullIndex = 0;
    int lastUnderfullIndex = 0;
    while (true) {
        while (entryList[lastOverfullIndex].probability <= baseProbability) {
            lastOverfullIndex++;
            if (lastOverfullIndex == size)
                return;
        }
        while (entryList[lastUnderfullIndex].probability >= baseProbability) {
            lastUnderfullIndex++;
            if (lastUnderfullIndex == size)
                return;
        }
        double delta = baseProbability - entryList[lastUnderfullIndex].probability;
        entryList[lastUnderfullIndex].probability = 1;
        entryList[lastOverfullIndex].probability -= delta;
        table.coinFlipReplacement[lastUnderfullIndex] = lastOverfullIndex;
        table.coinFlipProbability[lastUnderfullIndex] =
            (uint32_t)(delta / baseProbability * std::numeric_limits<uint32_t>::max());
        if (entryList[lastOverfullIndex].probability < baseProbability) {
            lastUnderfullIndex = std::min(lastUnderfullIndex, lastOverfullIndex);
        }
    }
}

Graph RmatGenerator::generate() {
    double n = (1 << scale);
    if (n <= reduceNodes) {
        throw std::runtime_error("Error, shall delete more nodes than the graph originally has");
    }
    // when nodes are deleted, all nodes have less neighbors
    count numEdges = n * edgeFactor * n * 1.0 / static_cast<double>(n - reduceNodes);
    count wantedEdges = (n - reduceNodes) * edgeFactor;
    Graph G(n - reduceNodes, weighted);
    double ab = a + b;
    double abc = ab + c;
    AliasTable table;
    generateTable(table, 64, a, b, c, 1 - a - b - c); // TODO: Dynamic table size.

    auto quadrant([&]() { // TODO: Remove the old code.
        double r = Aux::Random::probability();
        TRACE("r: ", r);

        if (r <= a) {
            return 0;
        } else if (r <= ab) {
            return 1;
        } else if (r <= abc) {
            return 2;
        } else
            return 3;
    });

    auto drawEdge([&]() { // TODO: Remove the old code.
        /*node u = 0;
        node v = 0;
        for (index i = 0; i < scale; ++i) {
            count q = quadrant();
            u = u << 1;
            v = v << 1;
            u = u | (q >> 1);
            v = v | (q & 1);
        }

        return std::make_pair(u, v);*/
        return table.sampleEdge(Aux::Random::getURNG(), (uint8_t)scale);
    });

    if (reduceNodes > 0) {
        std::vector<node> nodemap(n, 0);

        for (count deletedNodes = 0; deletedNodes < reduceNodes;) {
            node u = Aux::Random::index(n);
            if (nodemap[u] == 0) {
                nodemap[u] = none;
                ++deletedNodes;
            }
        }

        for (node i = 0, u = 0; i < n; ++i) {
            if (nodemap[i] == 0) {
                nodemap[i] = u;
                ++u;
            }
        }

        node u, v;
        if (weighted) {
            for (index e = 0; e < numEdges; ++e) {
                std::tie(u, v) = drawEdge();
                u = nodemap[u];
                v = nodemap[v];
                if (u != none && v != none) {
                    G.increaseWeight(u, v, defaultEdgeWeight);
                }
            }
        } else {
            while (G.numberOfEdges() < wantedEdges) {
                std::tie(u, v) = drawEdge();
                u = nodemap[u];
                v = nodemap[v];
                if (u != none && v != none && u != v && !G.hasEdge(u, v)) {
                    G.addEdge(u, v);
                }
            }
        }
    } else {
        if (weighted) {
            for (index e = 0; e < numEdges; ++e) {
                std::pair<node, node> drawnEdge = drawEdge();
                G.increaseWeight(drawnEdge.first, drawnEdge.second, defaultEdgeWeight);
            }
        } else {
            while (G.numberOfEdges() < wantedEdges) {
                std::pair<node, node> drawnEdge = drawEdge();
                if (!G.hasEdge(drawnEdge.first, drawnEdge.second)) {
                    G.addEdge(drawnEdge.first, drawnEdge.second);
                }
            }
        }
    }

    G.shrinkToFit();
    return G;
}

} /* namespace NetworKit */
