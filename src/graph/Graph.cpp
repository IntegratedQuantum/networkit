/*
 * Graph.cpp
 *
 *  Created on: 28.11.2012
 *      Author: cls
 */

#include "Graph.h"

namespace EnsembleClustering {


Graph::Graph() {
	this->stingerG = stinger_new();
}

Graph::~Graph() {
}

Graph::Graph(stinger* stingerG) {
	this->stingerG = stingerG;
}



stinger* Graph::asSTINGER() const {
	return this->stingerG;
}

void Graph::insertEdge(node u, node v, double weight, int64_t type,
		int64_t timestamp) {
	stinger_insert_edge_pair(this->stingerG, type, u, v, weight, timestamp);
}

bool Graph::hasEdge(node u, node v) const {
	int to = stinger_has_typed_successor(this->stingerG, this->defaultEdgeType, u, v);
	int back = stinger_has_typed_successor(this->stingerG, this->defaultEdgeType, v, u);
	return to && back;
}


double Graph::weight(node v) const {
	return stinger_vweight(this->stingerG, v);
}

double Graph::weight(edge uv) const {
	return stinger_edgeweight(this->stingerG, uv.first, uv.second,
			this->defaultEdgeType);

}




double Graph::weight(node u, node v) const {
	return stinger_edgeweight(this->stingerG, u, v, this->defaultEdgeType);
}

int64_t Graph::numberOfEdges() const {
	return stinger_total_edges(this->stingerG);
}


int64_t Graph::numberOfNodes() const {
	// TODO: is this sufficient? do isolated nodes have to be counted?
	return stinger_max_active_vertex(this->stingerG);
}

node Graph::firstNode() const {
	return 1;
}

int64_t Graph::degree(node u) const {
	int64_t deg = stinger_outdegree(this->stingerG, u);
	// each ndirected edge is represented by two directed edges
	assert (deg == stinger_indegree(this->stingerG, u));
	return deg;
}

double Graph::totalEdgeWeight() const {
	double total = 0.0;
	FORALL_EDGES_BEGIN((*this)) {
		total += this->weight(EDGE_SOURCE, EDGE_DEST);
	} FORALL_EDGES_END();
	return total;
}

node Graph::lastNode() const {
	return this->numberOfNodes();
}

} /* namespace EnsembleClustering */
