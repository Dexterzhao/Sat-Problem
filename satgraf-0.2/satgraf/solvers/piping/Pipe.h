#ifndef Pipe_h
#define Pipe_h

#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <string>
#include <sstream>
#include <iostream>

using namespace std;

class Pipe {
    public:
        static Pipe* getInstance();
        Pipe();
        ~Pipe();
        
        void openPipe(const string& filename);
        void writeToPipe(const string& output);
        void printClause(const string vars, int state);
        void printVar(const int id, int state, bool isDecisionVariable, int activity);
        void printConflict();
        
        enum VAR_STATES { VAR_ASSIGNED_TRUE, VAR_ASSIGNED_FALSE, VAR_UNASSIGNED };
        enum CLAUSE_STATES { CLAUSE_ADDED, CLAUSE_REMOVED };
        
    private:
        static Pipe* instance;
        string filename;
        int pipe;
        int conflictNumber;
};

#endif
