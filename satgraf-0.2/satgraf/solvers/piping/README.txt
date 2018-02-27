To use SATgraf with a custom solver, the following must be implemented/done in your solver:
    1. In your code, tell the Pipe class where your piped file will be. Ex: Pipe::getInstance()->openPipe("solvers/piping/myPipe.txt");
    2. To inform SATgraf of variables changing state, send the following to the pipe: Pipe::getInstance()->printVar(const int id, int state, bool isDecisionVariable, int activity)
        a. id = the variable id
        b. state = the possible states are defined in Pipe.h and are VAR_ASSIGNED_TRUE, VAR_ASSIGNED_FALSE, VAR_UNASSIGNED
        c. isDecisionVariable(optional) = will highlight this variable in SATgraf. Does not neccessarily have to be a decision variable but can be used to highlight any desired variable if that is desired.
        d. activity(optional) = the associated activity of a variable. Refers to conflict activity and will highlight decision variables with an activity greater than 0 a different color than those that are 0
    3. To inform SATgraf of the clauses being added or removed, do the following: Pipe::getInstance()->printClause(const string vars, int state)
        a. vars = a spaced string with all of the variables ids. Ex: 1 2 3 4 5
        b. state = the state of the clause. All of the states are defined in Pipe.h and are CLAUSE_ADDED, CLAUSE_REMOVED
    4. (Optional) To inform SATgraf of the conflicts in the solving of the instance, do the following when a conflict arises Pipe::getInstance()->printConflict(). This can be done before and after a clause arises in order to see the state of the SAT instance at both of those times. Could be used to see any specific event within the solver.
