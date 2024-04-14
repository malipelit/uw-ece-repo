#include <iostream>         //Takes care of input/output strems
#include <vector>           //In place of arrays for dynamic allocations
#include <regex>            //For input recognition                        
#include <string>           //To do work with strings
#include <queue>            //To make use of queue to keep track of visited nodes

#include <memory>
#include "minisat/core/SolverTypes.h"
#include "minisat/core/Solver.h"

using namespace std;
using namespace Minisat;

class a2
{

    private:
        
        int number_of_nodes;
        vector<vector<int>> neighbour;                          //Vector of vectors of integer values called neighbour                                
    
    public:
    
//Written below is constructor of class. neighbour has number_of_nodes + 1 to make sure things start from 1 instead of 0.

        a2(int number_of_nodes): number_of_nodes(number_of_nodes), neighbour(number_of_nodes + 1) {}

// Function to be able to access private variable from outside the class

    const vector<vector<int>>& getNeighbours() const
    {
        return neighbour;
    }

// Function to add edges to the vector to populate the graph before traversing and finding shortest path

    void edge(int source, int dest)
    {
        // For valid input, source and destination cannot be greater than the total number of nodes(Vertices) in the graph
        if((source <= number_of_nodes) && (dest <= number_of_nodes))
        {
            neighbour[source].push_back(dest);                  //Will add one node to the vector inside the vector of nodes. 
            neighbour[dest].push_back(source);                  //Maybe works similar to dictionary?
        }
        else
        {
            std::cout << "Error: Invalid Input" << std::endl;
        }
    }

//Making a boolean function that returns true if path exists and false if it doesnt

    bool pathExists(int source, int dest, vector<int> &before)
    {
        vector<bool> visited(number_of_nodes + 1, false);       //Vector to keep track of which node has been visited. False by default
        queue<int> q;                                           //To go to next node

        visited[source] = true;                                 //Start from source, we need to show that it has been visited
        q.push(source);                                         //Current node is not present, will make this current node

        while(!q.empty())
        {
            int u = q.front();
            q.pop();

            for(int v : neighbour[u])                           //V will take values that are neighbouring points of node u
            {
                if(!visited[v])
                {
                    visited[v] = true;
                    before[v] = u;                              // This means node u comes before v
                    q.push(v);                                  // We want the next node(v) to become the current node
                }
                if (v == dest)                                  // Finally when we get to the destination, do not continue the function
                {
                    return true;
                }
            }
        }

        return false;                                           // If we never reach the destination
    }

// Function to print shortest path

    void shortestPath(int source, int dest)
    {
        vector<int> before(number_of_nodes + 1, -1);            //Making vector of nodes that come before a current node. Initializing all values to -1 to show nothing before this node.
        
        // The following will only execute if the path from source to destination exists. If not, give error.

        if(pathExists(source, dest, before))                    //Should return true or false
        {
            vector<int> path;                                   //Keep track of the path taken
            int now = dest;                                     //The current vertex we are at now. Starting from destinaton
            
            while (now != -1)                                   //If current vertex becomes -1, we reached source
            {
                path.push_back(now);                            //Adding the current vertex to the path
                now = before[now];                              //Changing now to node before the current vertex
            }

            std::reverse(path.begin(), path.end());             //To reverse the oder of the path we found. This is done because the path we get is from destination to source

            //Now printing the path

            for (int i=0; i < int(path.size()); i++)
            {
                std::cout << path[i];
                if (i < int(path.size())-1)
                {
                    std::cout << "-";
                }
            }
            std::cout << endl;
        }
        else
        {
            std::cout << "Error: Path does not exist." << endl;
        }
    }

    void CNF(int numNodes) 
    {

        int k = numNodes;

        while (k > -1)
        {

            unique_ptr<Solver> solver(new Solver()); 
            vector<vector<Lit>> x(numNodes + 1, vector<Lit>(k + 1));

            // At least one vertex is the ith vertex in the vertex cover
            for (int i = 1; i <= k; i++)
            {
                vec<Lit> clauses_Literals;
                for (int j = 1; j <= numNodes; j++)
                {
                    x[j][i] = mkLit(solver->newVar());
                    clauses_Literals.push(x[j][i]);
                }
                solver->addClause(clauses_Literals);
            }

            // No one vertex can appear twice in a vertex cover
            for (int m = 1; m <= numNodes; m++)
            {
                for (int p = 1; p <= k; p++)
                {
                    for (int q = p + 1; q <= k; q++)
                    {
                        solver->addClause(~x[m][p], ~x[m][q]);
                    }
                }
            }

            // No more than one vertex appears in the mth position of the vertex cover
            for (int m = 1; m <= k; m++)
            {
                for (int p = 1; p <= numNodes; p++)
                {
                    for (int q = p + 1; q <= numNodes; q++)
                    {
                        solver->addClause(~x[p][m], ~x[q][m]);
                    }
                }
            }

            // Every edge is incident to at least one vertex in the vertex cover
            for (int u = 1; u < numNodes; u++)
            {
                for (int v : neighbour[u])
                {
                    vec<Lit> clauses_Literals;
                    for (int l = 1; l <= k; l++)
                    {
                        clauses_Literals.push(x[u][l]);
                        clauses_Literals.push(x[v][l]);
                    }
                    solver->addClause(clauses_Literals);
                }
            }

            // Solve the CNF formula
            bool res = solver->solve();

            if (res)
            {
                k--;
            }
            else
            {
                break;
            }
        }

        k++;

        unique_ptr<Solver> solver(new Solver());
        vector<vector<Lit>> x(numNodes + 1, vector<Lit>(k + 1));
        // At least one vertex is the ith vertex in the vertex cover
        for (int i = 1; i <= k; i++)
        {
            vec<Lit> clauses_Literals;
            for (int j = 1; j <= numNodes; j++)
            {
                x[j][i] = mkLit(solver->newVar());
                clauses_Literals.push(x[j][i]);
            }
            solver->addClause(clauses_Literals);
        }
        // No one vertex can appear twice in a vertex cover
        for (int m = 1; m <= numNodes; m++)
        {
            for (int p = 1; p <= k; p++)
            {
                for (int q = p + 1; q <= k; q++)
                {
                    solver->addClause(~x[m][p], ~x[m][q]);
                }
            }
        }
        // No more than one vertex appears in the mth position of the vertex cover
        for (int m = 1; m <= k; m++)
        {
            for (int p = 1; p <= numNodes; p++)
            {
                for (int q = p + 1; q <= numNodes; q++)
                {
                    solver->addClause(~x[p][m], ~x[q][m]);
                }
            }
        }
        // Every edge is incident to at least one vertex in the vertex cover
        for (int u = 1; u < numNodes; u++)
        {
            for (int v : neighbour[u])
            {
                vec<Lit> clauses_Literals;
                for (int l = 1; l <= k; l++)
                {
                    clauses_Literals.push(x[u][l]);
                    clauses_Literals.push(x[v][l]);
                }
                solver->addClause(clauses_Literals);
            }
        }

        // Solve the CNF formula
        bool res = solver->solve();
        // cout << k << endl;

        if (res)
        {
            vector<int> vertexCover;
            for (int i = 1; i <= numNodes; i++)
            {
                for (int j = 1; j <= k; j++)
                {
                    if (solver->modelValue(x[i][j]) == l_True)
                    {
                        vertexCover.push_back(i);
                    }
                }
            }
            for (int i = 0; i < (int)vertexCover.size(); i++)
            {
                cout << vertexCover[i];
                if (i < (int)vertexCover.size() - 1)
                {
                    cout << " ";
                }
            }
            cout << endl;
        }
    }

};

int main(int argc, char** argv) {

    int number_of_nodes = 0;
    int vertex = 0;                                              //To keep track of if command V was done before or not
    int edge_flag = 0;

    a2 obj(number_of_nodes);

    while(true){

        std::string input;
        getline(cin, input);

        // If we reach end of input, break out of loop

        if(cin.eof())
        {
            break;
        }

        // Regular expressions for Vertices, Edges and Shortest path commands

        std::regex Vpattern(R"(\bV\s+(\d+)\s*)");
        std::regex Epattern(R"(^E\s+\{(?:<(\d+),(\d+)>(?:,\s*<\d+,\d+>)*)?\}$)");
        std::regex Spattern(R"(^s\s+(\d+)\s+(\d+)\s*)");
        std::regex spacepattern(R"(^\s*)");

        // To store regular expression matches in a variable to be used later

        std::smatch matches;

        // To keep track of where the regular expressions are in order to match further as and when required for vertices, edges or shortest path
        
        string::const_iterator searchStart(input.cbegin());

        //Checking conditions for commands

        if(regex_match(input, matches, Vpattern))                //Enters if command matches Vertex input expression
        {
            vertex = 0;
            edge_flag = 0;

            if(int(stoi(matches[1].str())) <= 1)
            {
                std::cout << "Error: Enter 2 or more vertices." << std::endl;
                vertex = 0;
                continue;
            }
            vertex = 1;
            number_of_nodes = int(stoi(matches[1].str()));
            obj = a2(number_of_nodes);
        }
        else if (regex_match(input, matches, Epattern))          // Enters if command matches Edge input expression
        {
            std::regex edgepattern("<(\\d+),(\\d+)>");
            if (vertex == 0)
            {
                std::cout << "Error: Vertices dont exist" << std::endl;
                continue;
            }
            if (edge_flag == 1)
            {
                std::cout << "Error: Invalid Input" << std::endl;
                vertex = 0;
                edge_flag = 0;
                continue;
            }
            if(vertex == 1 && edge_flag == 0)
            {
                obj = a2(number_of_nodes);

                // The following will look for first instance of the edgepattern

                while (std::regex_search(searchStart,input.cend(),matches,edgepattern))
                {
                    int v1 = stoi(matches[1].str());            //To get the vertex value
                    int v2 = stoi(matches[2].str());
                    
                    // Accessing private variable from the class
                    
                    const vector<vector<int>>& neighbour = obj.getNeighbours();
                    
                    //Condition to check if the edge already exists.

                    for (int check : neighbour[v1])
                    {
                        if (check == v2)
                        {
                            std::cout << "Error: Invalid Input" << std::endl;
                            vertex = 0;
                            break;
                        }
                    }
                    if ((v1 <= number_of_nodes) && (v2 <= number_of_nodes) && (v1 != 0) && (v2 != 0) && (v1 != v2))
                    {
                        obj.edge(v1,v2);
                        edge_flag = 1;
                    }
                    else
                    {
                        std::cout << "Error: Invalid Input." << std::endl;
                        edge_flag = 0;
                        vertex = 0;
                        obj = a2(number_of_nodes);
                        break;
                    }
                    searchStart = matches.suffix().first;
                }
                obj.CNF(number_of_nodes);
            }
        }
        else if (regex_match(input, matches, Spattern))          // Enters if command matches Shortes path input expression
        {
            int source = stoi(matches[1].str());
            int dest = stoi(matches[2].str());

            if(vertex==0)
            {
                std::cout << "Error: Vertices dont exist" << std::endl;
                continue;
            }
            if (source > number_of_nodes || dest > number_of_nodes || source == 0 || dest == 0)
            {
                std::cout << "Error: Source or Destination does not exist." << std::endl;
                continue;
            }
            if (source==dest)
            {
                std::cout << "Error: Invalid Input." << std::endl;
            }
            else
            {
                obj.shortestPath(source, dest);                  //Function to print shortest path
            }   
        }
        else if (regex_match(input, matches, spacepattern))
        {
            continue;
        }
        else                                                     // Enters and shows error if command does not match any input expression
        {
            vertex = 0;
            std::cout << "Error: Invalid Input." << std:: endl;
        }

    }

    return 0;
}
