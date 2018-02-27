#include "Pipe.h"

Pipe* Pipe::instance = 0;

Pipe* Pipe::getInstance() {
    if (!instance) {
        instance = new Pipe();
    }
    
    return instance;
}

Pipe::Pipe() {
    conflictNumber = 0;
}

Pipe::~Pipe() {
    this->pipe = 0;
    this->instance = 0;
}

void Pipe::openPipe(const string& filename) {
    this->filename = filename;
    this->pipe = open(filename.c_str(), O_WRONLY);
}

void Pipe::writeToPipe(const string& output) {
    write(this->pipe, output.c_str(), output.length());
}

/**
 * Expecting vars to be a spaced string with all variable ids. Ex: 1 2 4 6
 */
void Pipe::printClause(const string vars, int state) {
    std::ostringstream ss;
    ss << "c";
    
    if (state == CLAUSE_ADDED) {
        ss << " +";
    } else if (state == CLAUSE_REMOVED) {
        ss << " -";
    }
    
    ss << " " << vars;
    
    ss << " 0\n";
    
    writeToPipe(ss.str());
}

void Pipe::printVar(const int id, int state, bool isDecisionVariable, int activity) {
    std::ostringstream ss;
    ss << "v";
    
    if (isDecisionVariable) {
        ss << " d"; // Decision variable
    } else {
        ss << " p"; // Propagated variable
    }
    
    if (state == VAR_UNASSIGNED) {
        ss << " 2 ";
    } else if (state == VAR_ASSIGNED_TRUE) {
        ss << " 1 ";
    } else if (state == VAR_ASSIGNED_FALSE) {
        ss << " 0 ";
    }
    
    if (activity < 0) {
      activity = 0;
    }
    
    ss << activity << " ";
    ss << id+1 << "\n";
    
    writeToPipe(ss.str());
}

void Pipe::printConflict() {
    conflictNumber++;

    std::ostringstream ss;
    ss << "! " << conflictNumber << "\n";
    writeToPipe(ss.str());
}
