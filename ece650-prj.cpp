// Importing Neccessary header files

#include <iostream>                   // takes care of input/output streams
#include <vector>                     // Alternative of Array to do dynamic operations
#include <queue>                      // to iterate adjacency list
#include <regex>                      // to deal with input formats
#include <climits>                    // for infinite or INT_MAX value
#include <string>                     // For String Operations
#include <pthread.h>                  // for timing
#include <time.h>                     // Timing & Code Benchmarking
#include <map>                        // Storing Runtimes
#include <fstream>                    // write to csv file
#include <thread>                     // for Multi Threading (Parallel Processing)
#include <mutex>                      // To lock the resources so that output dont interleave
#include <algorithm>                  // sorting Algorithms
#include <memory>                     // defined std::unique_ptr
#include "minisat/core/SolverTypes.h" // defines Var and Lit
#include "minisat/core/Solver.h"      // defines Solver

using namespace std;     // a scope to the identifiers of Minisat Library
using namespace Minisat; // a scope to the identifiers of Minisat library

int timeout_count = 1;

vector<int> output_CNF;
vector<int> output_VC1;
vector<int> output_VC2;

//=================PART OF ANALYSIS STARTS====================================
vector<int> vertexCoverCNF;
vector<int> vertexCoverAPPROX1;
vector<int> vertexCoverAPPROX2;
vector<long> CNF_runtimes;
vector<long> VC1_runtimes;
vector<long> VC2_runtimes;
vector<double> CNF_approx_ratio;
vector<double> VC1_approx_ratio;
vector<double> VC2_approx_ratio;
//=================PART OF ANALYSIS ENDS====================================

vector<int> vertice_list;

//========================================= MAIN ===================================================
class Project
{
    private:
        vector<vector<int>> adjList;            // Vector list to store adjacency list

    public:
        int number_of_nodes;                    // Number of Vertices
        
        Project(int number_of_nodes) : 
            number_of_nodes(number_of_nodes), 
            adjList(number_of_nodes + 1) {}     // Initialising the list

    // Function to be able to access private variable from outside the class

    const vector<vector<int>>& getNeighbours() const
    {
        return adjList;
    }

    void edge(int src, int dest)
    {
        // For valid input, source and destination cannot be greater than the total number of nodes(Vertices) in the graph
        if ((number_of_nodes >= src) && (number_of_nodes >= dest))
        {
            adjList[src].push_back(dest);               //Will add one node to the vector inside the vector of nodes.
            adjList[dest].push_back(src);               //Maybe works similar to dictionary?
        }
        else
        {
            std::cout << "Error: Invalid Vertex Input" << std::endl;
        }
    }

    //Making a boolean function that returns true if path exists and false if it doesnt

    bool pathExists(int src, int dest, vector<int> &pred, vector<int> &dist)
    {
        vector<bool> visited(number_of_nodes + 1, false);          //Vector to keep track of which node has been visited. False by default
        queue<int> q;                                       //To go to next node

        visited[src] = true;                                //Start from source, we need to show that it has been visited
        dist[src] = 0;
        q.push(src);                                        //Current node is not present, will make this current node

        while (!q.empty())
        {
            int u = q.front();
            q.pop();

            for (int v : adjList[u])                        //V will take values that are neighbouring points of node u
            {
                if (!visited[v])
                {
                    visited[v] = true;
                    dist[v] = dist[u] + 1;
                    pred[v] = u;                            // This means node u comes before v
                    q.push(v);                              // We want the next node(v) to become the current node

                    if (v == dest)                          // Finally when we get to the destination, do not continue the function
                    {
                        return true;
                    }
                }
            }
        }

        return false;                                       // If we never reach the destination
    }

    // Function to print shortest path

    void shortestPath(int start, int end)
    {
        vector<int> pred(number_of_nodes + 1, -1);                 //Making vector of nodes that come before a current node. Initializing all values to -1 to show nothing before this node.
        vector<int> dist(number_of_nodes + 1, INT_MAX);

        // The following will only execute if the path from source to destination exists. If not, give error.

        if (pathExists(start, end, pred, dist))             //Should return true or false
        {
            vector<int> path;                               //Keep track of the path taken
            int current = end;                              //The current vertex we are at now. Starting from destinaton

            while (current != -1)                           //If current vertex becomes -1, we reached source
            {
                path.push_back(current);                    //Adding the current vertex to the path
                current = pred[current];                    //Changing now to node before the current vertex
            }

            reverse(path.begin(), path.end());              //To reverse the oder of the path we found. This is done because the path we get is from destination to source

            //Now printing the path

            for (int i = 0; i < (int)path.size(); ++i)
            {
                cout << path[i];
                if (i < (int)path.size() - 1)
                {
                    cout << "-";
                }
            }
            cout << endl;
        }
        else
        {
            cout << "Error: Given source and destination are not connected" << endl;
        }
    }

    // This time we return the vertex cover back which is a vector of integers, so function will also be of that type

    vector<int> CNF(int number_of_nodes, vector<vector<int>> adjList, int k) 
    {
        unique_ptr<Solver> solver(new Solver());
        vector<vector<Lit>> x(number_of_nodes + 1, vector<Lit>(k + 1));
       
        //  At least one vertex is the ith vertex in the vertex cover
        for (int i = 1; i <= k; i++)
        {
            vec<Lit> clauses_Literals;
            for (int j = 1; j <= number_of_nodes; j++)
            {
                x[j][i] = mkLit(solver->newVar());
                clauses_Literals.push(x[j][i]);
            }
            solver->addClause(clauses_Literals);
        }
        
        //  No one vertex can appear twice in a vertex cover
        for (int m = 1; m <= number_of_nodes; m++)
        {
            for (int p = 1; p <= k; p++)
            {
                for (int q = p + 1; q <= k; q++)
                {
                    solver->addClause(~x[m][p], ~x[m][q]);
                }
            }
        }
        
        //  No more than one vertex appears in the mth position of the vertex cover
        for (int m = 1; m <= k; m++)
        {
            for (int p = 1; p <= number_of_nodes; p++)
            {
                for (int q = p + 1; q <= number_of_nodes; q++)
                {
                    solver->addClause(~x[p][m], ~x[q][m]);
                }
            }
        }
        
        //  Every edge is incident to at least one vertex in the vertex cover
        for (int u = 1; u < number_of_nodes; u++)
        {
            for (int v : adjList[u])
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

        vector<int> vertexCover;
        if (res)
        {
            for (int i = 1; i <= number_of_nodes; i++)
            {
                for (int j = 1; j <= k; j++)
                {
                    if (solver->modelValue(x[i][j]) == l_True)
                    {
                        vertexCover.push_back(i);
                    }
                }
            }
        }
        return vertexCover;
    }

    void runApproxVC1(int number_of_nodes, vector<vector<int>> adjList_VC1)
    {
        struct timespec start, end;
        clockid_t clock_id;
        pthread_getcpuclockid(pthread_self(), &clock_id);
        clock_gettime(clock_id, &start);

        bool reductionOccurred = true;

        while (reductionOccurred)
        {
            reductionOccurred = false;

            int maxDegreeVertex = -1;
            int maxDegree = -1;

            for (int i = 1; i <= number_of_nodes; ++i)
            {
                int degree = adjList_VC1[i].size();
                if (degree > maxDegree && degree != 0)
                {
                    maxDegree = degree;
                    maxDegreeVertex = i;
                }
            }

            if (maxDegreeVertex == -1)
                break;

            vertexCoverAPPROX1.push_back(maxDegreeVertex);

            // Remove edges incident on the selected vertex
            for (int neighbor : adjList_VC1[maxDegreeVertex])
            {
                for (auto it = adjList_VC1[neighbor].begin(); it != adjList_VC1[neighbor].end();)
                {
                    if (*it == maxDegreeVertex)
                    {
                        it = adjList_VC1[neighbor].erase(it);
                        reductionOccurred = true;
                    }
                    else
                    {
                        ++it;
                    }
                }
            }

            // Remove the selected vertex and its incident edges
            adjList_VC1[maxDegreeVertex].clear();
        }

        sort(vertexCoverAPPROX1.begin(), vertexCoverAPPROX1.end());

        clock_gettime(clock_id, &end);
        long sec = end.tv_sec - start.tv_sec;
        long nsec = end.tv_nsec - start.tv_nsec;
        long elapsed_time_micro = sec * 1000000 + nsec / 1000;
        VC1_runtimes.push_back(elapsed_time_micro);
        pthread_exit(NULL);
    }

    void runApproxVC2(int number_of_nodes, vector<vector<int>> adjList_VC2)
    {
        struct timespec start, end;
        clockid_t clock_id;
        pthread_getcpuclockid(pthread_self(), &clock_id);
        clock_gettime(clock_id, &start);

        while (true)
        {
            bool foundEdge = false;
            for (int u = 1; u <= number_of_nodes; u++)
            {
                for (int v : adjList_VC2[u])
                {
                    if ((u != 0) && (v != 0) && (adjList_VC2[v].size() != 0) && (adjList_VC2[u].size() != 0))
                    {
                        foundEdge = true;
                        vertexCoverAPPROX2.push_back(u);
                        vertexCoverAPPROX2.push_back(v);

                        // // Remove edges incident on u and v
                        adjList_VC2[u].clear();
                        adjList_VC2[v].clear();
                    }
                }
            }

            if (!foundEdge)
                break;
        }

        sort(vertexCoverAPPROX2.begin(), vertexCoverAPPROX2.end());

        clock_gettime(clock_id, &end);
        long sec = end.tv_sec - start.tv_sec;
        long nsec = end.tv_nsec - start.tv_nsec;
        long elapsed_time_micro = sec * 1000000 + nsec / 1000;
        VC2_runtimes.push_back(elapsed_time_micro);
        pthread_exit(NULL);
    }

    vector<int> VC_Binary_Search(int k_low,int k_high)
    {
         
        vector<int> vertex_cover_binary;
        vector< vector< int > > empty_adjList(number_of_nodes+1);
        
        while(k_low<=k_high)
        {
            int mid = floor((k_low+k_high)/2);
            vector<int> vc = CNF(number_of_nodes, adjList, mid);
            if(vc.size() == 0 && adjList != empty_adjList)
            {
                k_low = mid+1;
            }
            else
            {
                vertex_cover_binary = vc;
                k_high = mid-1;
            }
        }
        return vertex_cover_binary;
    }
};

void* threadFunction1(void* graph) {
    Project* myObj = static_cast<Project*>(graph);

    struct timespec start, end;
    clockid_t clock_id;
    pthread_getcpuclockid(pthread_self(), &clock_id);
    clock_gettime(clock_id, &start);

    if(timeout_count) {
        vertexCoverCNF = myObj->VC_Binary_Search(-1, myObj->number_of_nodes);


        clock_gettime(clock_id, &end);
        long sec = end.tv_sec - start.tv_sec;
        long nsec = end.tv_nsec - start.tv_nsec;
        long elapsed_time_micro = sec * 1000000 + nsec / 1000;
        CNF_runtimes.push_back(elapsed_time_micro);
    }
    else {
        long elapsed_time_micro = 3 * 100000000;
        CNF_runtimes.push_back(elapsed_time_micro);
    }

    pthread_exit(NULL);
    return nullptr;
}

void* threadFunction2(void* graph) {
    Project* myObj = static_cast<Project*>(graph);
    myObj->runApproxVC1(myObj->number_of_nodes, myObj->getNeighbours());
    return nullptr;
}

void* threadFunction3(void* graph) {
    Project* myObj = static_cast<Project*>(graph);
    myObj->runApproxVC2(myObj->number_of_nodes, myObj->getNeighbours());
    return nullptr;
}

// main function
int handle_IO()
{
    int number_of_nodes = 0;
    int vertex = 0;
    int e_flag = 0;

    Project graph(number_of_nodes);
    mutex mtx;

    while (true)
    {
        string input;
        if (cin.eof())
        {
            break;
        }

        getline(cin, input);

        if (input.empty())
        {
            continue;
        }

        std::regex Vpattern(R"(\bV\s+(\d+)\s*)");
        std::regex Epattern(R"(^E\s+\{(?:<(\d+),(\d+)>(?:,\s*<\d+,\d+>)*)?\}$)");
        std::regex Spattern(R"(^s\s+(\d+)\s+(\d+)\s*)");
        std::regex spacepattern(R"(^\s*)");

        smatch matches;
        string::const_iterator searchStart(input.cbegin());

        if (regex_match(input, matches, Vpattern))
        {
            vertex = 0;
            e_flag = 0;

            if(int(stoi(matches[1].str())) <= 1)
            {
                std::cout << "Error: Enter 2 or more vertices." << std::endl;
                vertex = 0;
                continue;
            }
            vertex = 1;
            number_of_nodes = int(stoi(matches[1].str()));
            graph = Project(number_of_nodes);
            vertice_list.push_back(number_of_nodes);
        }
        else if (regex_match(input, matches, Epattern))
        {

            regex pattern("<(\\d+),(\\d+)>");
            if (vertex == 0)
            {
                std::cout << "Error: Vertices dont exist" << std::endl;
                continue;
            }
            if (e_flag == 1)
            {
                std::cout << "Error: Invalid Input" << std::endl;
                vertex = 0;
                e_flag = 0;
                continue;
            }
            if (vertex == 1 && e_flag == 0)
            {
                graph = Project(number_of_nodes);
                while (std::regex_search(searchStart, input.cend(), matches, pattern))
                {
                    int xi = stoi(matches[1].str());
                    int yi = stoi(matches[2].str());

                    // Accessing private variable from the class
                    
                    const vector<vector<int>>& neighbour = graph.getNeighbours();
                    
                    //Condition to check if the edge already exists.

                    for (int check : neighbour[xi])
                    {
                        if (check == yi)
                        {
                            std::cout << "Error: Invalid Input" << std::endl;
                            vertex = 0;
                            break;
                        }
                    }
                    if ((xi <= number_of_nodes) && (yi <= number_of_nodes) && (xi != 0) && (yi != 0) && (xi != yi))
                    {
                        graph.edge(xi,yi);
                        e_flag = 1;
                    }
                    else
                    {
                        std::cout << "Error: Invalid Input." << std::endl;
                        e_flag = 0;
                        vertex = 0;
                        graph = Project(number_of_nodes);
                        break;
                    }
                    searchStart = matches.suffix().first;
                }
            }
            
            vertexCoverCNF.clear();
            vertexCoverAPPROX1.clear();
            vertexCoverAPPROX2.clear();

            pthread_t t1,t2,t3;
            pthread_create(&t1, nullptr, &threadFunction1, &graph);
            pthread_create(&t2, nullptr, &threadFunction2, &graph);
            pthread_create(&t3, nullptr, &threadFunction3, &graph);

            struct timespec timeout;
            clock_gettime(CLOCK_REALTIME, &timeout);
            timeout.tv_sec += 60;

            // Wait for the cnf_thread to finish or timeout
            int join_result = pthread_timedjoin_np(t1, nullptr, &timeout);

            
            if(join_result == ETIMEDOUT) {
                long elapsed_time_micro = 3 * 100000000;
                CNF_runtimes.push_back(elapsed_time_micro);
            }

            if(join_result == ETIMEDOUT || timeout_count == 0)
            {
                cout<<"CNF-SAT-VC: timeout"<<endl;
                timeout_count = 0;
            }
            else {
                pthread_join(t1, nullptr);
                cout << "CNF-SAT-VC: ";
                for (int i = 0; i < (int)vertexCoverCNF.size(); i++)
                {
                    cout << vertexCoverCNF[i];
                    output_CNF.push_back(vertexCoverCNF[i]);
                    if (i < (int)vertexCoverCNF.size() - 1)
                    {
                        cout << ",";
                    }
                }
                cout << endl;
            }

            pthread_join(t2, nullptr);
            pthread_join(t3, nullptr);
        

            cout << "APPROX-VC-1: ";
            for (int i = 0; i < (int)vertexCoverAPPROX1.size(); i++)
            {
                cout << vertexCoverAPPROX1[i];
                output_VC1.push_back(vertexCoverAPPROX1[i]);
                if (i < (int)vertexCoverAPPROX1.size() - 1)
                {
                    cout << ",";
                }
            }
            cout << endl;

            cout << "APPROX-VC-2: ";
            for (int i = 0; i < (int)vertexCoverAPPROX2.size(); i++)
            {
                cout << vertexCoverAPPROX2[i];
                output_VC2.push_back(vertexCoverAPPROX2[i]);
                if (i < (int)vertexCoverAPPROX2.size() - 1)
                {
                    cout << ",";
                }
            }
            cout << endl;
            
            //=========================== ANALYSIS PART START====================================================

            
            int x_min = min(min((int)output_CNF.size(), (int)output_VC1.size()), (int)output_VC2.size());

            // Print approximation ratio
            if(x_min != 0)
            {
            CNF_approx_ratio.push_back((double)output_CNF.size() / x_min);
            VC1_approx_ratio.push_back((double)output_VC1.size() / x_min);
            VC2_approx_ratio.push_back((double)output_VC2.size() / x_min);

            }
            else
            {
            CNF_approx_ratio.push_back((double)output_CNF.size() / output_VC1.size());
            VC1_approx_ratio.push_back((double)output_VC1.size() / output_VC1.size());
            VC2_approx_ratio.push_back((double)output_VC2.size() / output_VC1.size());
            }

    

            ofstream myfile;
            myfile.open("../runtime.csv");
            myfile << "graphspec,vertices,CNF,VC1,VC2\n";
            for (int i = 0; i < (int)CNF_runtimes.size(); i++)
            {
                myfile << i + 1 << "," << vertice_list[i] << "," << CNF_runtimes[i] << "," << VC1_runtimes[i] << "," << VC2_runtimes[i] << "\n";
            }
            myfile.close();


            ofstream myfile2;
            myfile2.open("../approx_ratio.csv");
            myfile2 << "graphspec,vertices,CNF,VC1,VC2\n";
            for (int i = 0; i < (int)CNF_approx_ratio.size(); i++)
            {
                myfile2 << i + 1 << "," << vertice_list[i] << "," << CNF_approx_ratio[i] << "," << VC1_approx_ratio[i] << "," << VC2_approx_ratio[i] << "\n";
            }
            myfile2.close();
            

            // Clear Vectors before adding data for another graph spec
            output_CNF.clear();
            output_VC1.clear();
            output_VC2.clear();
            

            //==========================ANALYSIS PART ENDS==============================================
        }
        else if (regex_match(input, matches, Spattern))
        {
            int start = stoi(matches[1].str());
            int end = stoi(matches[2].str());

            if(vertex==0)
            {
                std::cout << "Error: Vertices dont exist" << std::endl;
                continue;
            }
            if (start > number_of_nodes || end > number_of_nodes || start == 0 || end == 0)
            {
                cout << "Error: Given source or destination do not exist." << endl;
                continue;
            }

            if (start == end)
            {
                std::cout << "Error: Invalid Input." << std::endl;
            }
            else
            {
                graph.shortestPath(start, end);
            }
        }
        else if (regex_match(input, matches, spacepattern))
        {
            continue;
        }
        else
        {
            vertex = 0;
            cout << "Error: Invalid Input Format" << endl;
        }
    }

    return 0;
}

void* t_handle_IO(void* args){
    handle_IO();
    return nullptr;
}

int main(){
    // Thread 1
    pthread_t thread_IO;
    pthread_create(&thread_IO, NULL, t_handle_IO, NULL);
    pthread_join(thread_IO, NULL);

    return 0;
}