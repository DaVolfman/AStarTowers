/**
 * @file towers.cpp
 * @author Steven Clark
 * @date 12/10/2017
 * @brief Source code for A* solver for Towers of Hanoi
 */

#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <sstream>

using std::string;
using std::vector;
using std::multimap;
using std::map;
using std::cout;
using std::endl;

/*
//not needed
unsigned int tfact(unsigned int n, unsigned int const trunc = 1){
	unsigned int rval = 1;
	while( n > trunc)
		rval *= n--;
	return rval;
}*/

int numrings = 3;
int bitmask = (1 << numrings) - 1;

/**
 * @brief Towers of Hanoi game state
 */
class towerstate{
protected:
	int peg1;
	int peg2;
	int peg3;

	towerstate(int p1, int p2, int p3){
		peg1 = p1;
		peg2 = p2;
		peg3 = p3;
	}


public:
	//static towerstate errorstate = towerstate(-1,-1,-1);//this doesn't work


	///@brief Construct a new state with all rings on the first peg
	towerstate(){
		peg1 = bitmask;
		peg2 = 0;
		peg3 = 0;
	}

	///@brief Less than operator for placement in ordered data structures
	///@note necessary for use as an STL map or set key
	bool operator<(const towerstate &other) const{
		return (peg1 == other.peg1)?((peg2 == other.peg2) ? (peg3 < other.peg3) :(peg2 < other.peg2) ) :(peg1 < other.peg1);
	}

	bool operator==(const towerstate &other) const{
		return (peg1 == other.peg1) and (peg2 == other.peg2) and (peg3 == other.peg3);
	}

	bool operator!=(const towerstate &other) const{
		return (peg1 != other.peg1) or (peg2 != other.peg2) or (peg3 != other.peg3);
	}

	bool isWinning()const{//all rings are on a goal peg
		return peg2 == bitmask or peg3 == bitmask;
	}

	bool isError() const{
		return (peg1 < 0) or (peg2 <0) or (peg3 < 0);
	}

	/// @brief can move number m be legally taken
	/// @param m the number of the move to take in order 1to2, 2to3, 3to1, 2to1, 3to2, 1to3
	/// @return True if move @p m is a legal move
	bool canMove(const int m)const{
		//The find first set builtin function returns the number (1-based index)
		//of the least significant one bit of an integer, but return zero if the
		//integer is zero.  So we're using a conditional to preserve ordinality
		int a = (!peg1) ? 33 : __builtin_ffs(peg1);
		int b = (!peg2) ? 33 : __builtin_ffs(peg2);
		int c = (!peg3) ? 33 : __builtin_ffs(peg3);

		//return true if the smallest ring on the start is smaller than the one on the destination
		switch (m){
		case 0:
			return a < b;
		case 1:
			return b < c;
		case 2:
			return c < a;
		case 3:
			return a > b;
		case 4:
			return b > c;
		case 5:
			return c > a;
		default:
			return false;
		}
	}

	/// @brief Make a new problem state with the given move taken from this one.
	/// @param m the number of the move to take in order 1to2, 2to3, 3to1, 2to1, 3to2, 1to3
	/// @return a new problem state with the given move number taken, an error state if not legal
	towerstate makeMove(const int m)const{
		towerstate rval = *this;

		//The find first set builtin function return the number (1-based index)
		//of the least significant one bit of an integer, but return zero if the
		//integer is zero.  So we're using a conditional to preserve ordinality
		int a = (!peg1) ? 33 : __builtin_ffs(peg1);
		int b = (!peg2) ? 33 : __builtin_ffs(peg2);
		int c = (!peg3) ? 33 : __builtin_ffs(peg3);

		a--;//turn into indices
		b--;
		c--;

		if(! canMove(m))
			return towerstate(-1,-1,-1);

		switch (m){
		case 0://remove the lowest value ring from peg1 and add to peg 2
			rval.peg1 ^= (1 << a);
			rval.peg2 ^= (1 << a);
			return rval;
		case 1://from peg2 to peg3
			rval.peg2 ^= (1 << b);
			rval.peg3 ^= (1 << b);
			return rval;
		case 2://from peg3 to peg1
			rval.peg3 ^= (1 << c);
			rval.peg1 ^= (1 << c);
			return rval;
		case 3://from peg 2 to peg 1
			rval.peg2 ^= (1 << b);
			rval.peg1 ^= (1 << b);
			return rval;
		case 4://from peg 3 to peg 2
			rval.peg3 ^= (1 << c);
			rval.peg2 ^= (1 << c);
			return rval;
		case 5://from peg 1 to peg 3
			rval.peg1 ^= (1 << a);
			rval.peg3 ^= (1 << a);
			return rval;
		}


		return towerstate(-1,-1,-1);
	}

	///@brief Computes a heuristic for all items to reach a goal peg
	int h()const{
		int rval = 1 << numrings;
		//get the number of rings that have ever been moved from peg 1 by counting the number of leading
		//ones before the first zero on peg1 within the problem space.  Subtract the number of bits outside
		//the problem space
		//builtin CLZ is undefined for a zero so we need to wrap the case where that happens in a conditional
		int a = (peg1 == bitmask) ? 0 : (32 - __builtin_clz(~(~bitmask | peg1)) );

		//get the largest ring on both peg1 and peg2 by counting the leading zeros until it's bit is found
		//and subtract that from the number of bits in the data format
		//again we need to wrap the zero case in a conditional
		int b = (peg2 == 0) ? 0 : (32 - __builtin_clz(peg2));
		int c = (peg3 == 0) ? 0 : (32 - __builtin_clz(peg3));

		rval -= 1 << a;

		//add back in the optimistic bare minimum time to consolidate all moved rings onto the current
		//highest goal peg so we can move another ring off the starting peg onto a blank
		//AKA the number of rings we've ever moved - the number of rings on the highest goal peg
		if(b > c){
			rval += (a - __builtin_popcount(peg2));
		}else if(c > b){
			rval += (a - __builtin_popcount(peg3));
		}

		return rval;
	}

	///@brief Get all legal game states that can be expanded from this one
	///@return a vector of states one move from this one
	vector <towerstate> nextStates()const{
		vector <towerstate> rvec;
		for(int i = 0; i < 6; ++i){
			if(canMove(i))
				rvec.push_back(makeMove(i));
		}
		return rvec;
	}
	///@brief Get a string representation of the problem state.
	string toString()const{
		std::ostringstream sbuilder;

		for(int i = 0; i < 31; ++i){
			if( (1 << i) & peg1)
				sbuilder << i+1 << "-";
		}
		sbuilder << "|";
		for(int i = 0; i < 31; ++i){
			if( (1 << i) & peg2)
				sbuilder << i+1 << "-";
		}
		sbuilder << "|";
		for(int i = 0; i < 31; ++i){
			if( (1 << i) & peg3)
				sbuilder << i+1 << "-";
		}
		//sbuilder << std::hex << peg1 << "|" << std::hex << peg2 << "|" << std::hex << peg3;
		return sbuilder.str();
	}
};

/**
 * @brief A fully generated problem space graph node with A* information
 */
struct PSNode {
	towerstate state;///<problem state itself
	PSNode * parent;///<parent node in the problem space graph if any
	int cost2reach;///<the number of moves taken to reach this node from the start, g()
	int projectedCost;///<the heuristic estimate number of moves to complete the problem, h()
	vector <PSNode *> children;///<the child nodes in the problem space graph

	///@brief New problem space graph node given problem state and parent node.
	PSNode(towerstate newstate, PSNode * from){
		state = newstate;
		parent = from;
		if(NULL == from)
			cost2reach = 0;
		else
			cost2reach = from->cost2reach + 1;
		projectedCost = state.h();
	}

	///@brief Update the cost to reach this node (and any children) if new cost is better.
	///@param newcost The cost of the new path to this node found.
	///@param newparent The node to backtrack along this new path.
	///@param frontier The frontier of the problem space graph to update  with a new f if neccesary
	///@return True if the new path was supperior on the path was updated
	bool updateCostCond(int newcost, PSNode * newparent, multimap<int, PSNode *> &frontier){
		if(newcost < cost2reach){
			//look for node in frontier
			for(multimap<int, PSNode*>::iterator iter = frontier.lower_bound(cost2reach); iter != frontier.upper_bound(cost2reach); iter++){
				if(iter->second == this){
					frontier.erase(iter);//if in frontier remove it and emplace with new adjusted cost
					frontier.insert(std::pair<int,PSNode *>(newcost+projectedCost,this));
					break;
				}
			}

			cost2reach = newcost;
			parent = newparent;

			//update any children
			for(unsigned int i = 0; i < children.size(); ++i){
				children[i]->updateCostCond(newcost + 1, this, frontier);
			}
			return true;
		}
		return false;
	}
};

//used to simplify template syntax
typedef std::pair<int,PSNode *> FrontierPair;
typedef std::pair<towerstate, PSNode *> GeneratedPair;

int main(int argc, char** argv){
	PSNode * winningNode = NULL;

	//map of all generated gamestates to their problem space graph nodes
	map <towerstate, PSNode *> generated;

	//map of all frontier nodes by their f() costs
	multimap <int, PSNode *> frontier;

	//if there are arguments attempt to update the number of rings from the first argument
	if(argc == 2){
		std::istringstream argument(argv[1]);
		int tempnumrings = -1;
		argument >> tempnumrings;

		if(tempnumrings > 1){
			numrings = tempnumrings;
			bitmask = (1 << numrings)-1;
		}
	}

	//node currently being evaluated, begins at problem start state;
	PSNode *tempNode = new PSNode(towerstate(),NULL);
	PSNode * workNode = NULL;//just a temp
	string outpath, tempstring;//temps for formatting output of the wining path

	//Add start state to generated nodes and frontier
	generated.insert(GeneratedPair(tempNode->state, tempNode));
	frontier.insert(FrontierPair(tempNode->projectedCost,tempNode));

	//While we haven't won or lost
	while(winningNode == NULL and ! frontier.empty()){

		//output the current frontier nodes
		cout << "Frontier nodes are:\n";
		for(multimap<int, PSNode*>::iterator iter = frontier.begin();
				iter != frontier.end(); ++iter){
			cout << iter->second->state.toString()
					<< " h="<< iter->second->projectedCost
					<< " g="<< iter->second->cost2reach
					<< " f="<< iter->first << endl;
		}

		//chose the node with the lowest cost in the frontier
		tempNode = frontier.begin()->second;
		cout << "Expand:\t" << tempNode->state.toString() << endl;

		//expand it
		frontier.erase(frontier.begin());
		vector<towerstate> tempChildren = tempNode->state.nextStates();
		for(unsigned int i = 0; winningNode == NULL and i < tempChildren.size();++i){
			if(tempChildren[i] != tempNode->state){//if generated state not that of parent
				cout << "Generated:\t" << tempChildren[i].toString() << '\t';

				//if state in question is already generated, updated if neccesary
				if(generated.count(tempChildren[i]) > 0){
					cout << "Regenerated\t";
					if(generated[tempChildren[i]]->updateCostCond(tempNode->cost2reach+1, tempNode, frontier))
						cout << "Updated F\t";
					else
						cout << "No update\t";
				}else{//generate the graph node for this state
					cout << "New node\t        \t";
					workNode = new PSNode(tempChildren[i],tempNode);
					generated.insert(GeneratedPair(workNode->state,workNode));
					frontier.insert(FrontierPair(workNode->cost2reach + workNode->projectedCost,workNode));
					if(workNode->state.isWinning()){
						winningNode = workNode;
					}
				}

				//Add the node, generated or new to the children of tempNode
				tempNode->children.push_back(generated[tempChildren[i]]);

				cout << "g=" << generated[tempChildren[i]]->cost2reach
						<< " h=" << generated[tempChildren[i]]->projectedCost
						<< " f=" << generated[tempChildren[i]]->cost2reach + generated[tempChildren[i]]->projectedCost
						<< endl;
			}

		}
	}

	//If the winning path was found, print it
	if(winningNode != NULL){
		cout << "Winning state reached." << endl;
		for(workNode = winningNode; workNode != NULL; workNode = workNode->parent){
			outpath = workNode->state.toString() + outpath;
			if(workNode->parent != NULL)
				outpath = " -> " + outpath;
		}
		cout << outpath << endl;
	}else{
		cout << "No path to goal!" << endl;
	}

	//remove all nodes in the problem space graph from the heap
	for(map <towerstate, PSNode *>::iterator iter = generated.begin(); iter != generated.end(); ++iter){
		delete iter->second;
	}
	return 0;
}
