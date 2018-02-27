#Dependencies:
SATGraf is the graphical UI for visualising the evolution of a SAT solver. It uses [SATLib](https://bitbucket.org/znewsham/satlib) as the backend for strucural information and evolution data.
Validation is provided by the [ValidatedCL](https://bitbucket.org/znewsham/validatedcl) package.

If compiling from source, these packages are required.
 
#Installation:     
    unzip satgraf.zip   
    cd satgraf   
    cd solvers/minisat   
    make   
    cd ../../   

#Notes:   
    The fgpu option is under development and may not work fully. 
    The circle layout algorithm works poorly with disjoint graphs.
    The Louvian method requires a non disjoint graph
    Either -f or -u must be specified.   
    
#Usage: java -jar SatGraf.jar [com|imp|evo|evo_data|generate|generateOne] <options>

##com - View the static community representation of the formula.   
	-f --file(default = null) The file (either .cnf or .sb)   
	Must be an existing file For which you have: read permissions   
	-u --url(default = null) A file URL (either .cnf or .sb)   
	-c --community(default = ol) The community detection algorithm   
	Must be one of:    
		l - The Louvian community detection algorithm   
		ol - The Online community detection algorithm   
		cnm - The Clauset-Neuman-Moore community detection algorithm   
	-p --pattern(default = null) A list of regex expressions to group variables (not yet implemented)   
	-l --layout(default = f) The layout algorithm to use   
	Must be one of:    
		f - An implementation of the Fruchtermon and Reingold force directed layout algorithm   
		fgpu - A GPU implementation of the Fruchtermon and Reingold force directed layout algorithm   
		kk - An implementation of the Kamada-Kawai placement algorithm   
		c - A basic layout algorithm, nodes are layed out within a community using the FR layout algorithm. The communities are then layed out in a circle, with those most connected next to each other.   
		grid - A basic layout algorithm, nodes are layed out within a community in a grid pattern. The communities are then layed out on a grid   
		gkk - A basic layout algorithm, nodes are layed out within a community using the KK algorithm. The communities are then layed out on a grid   
		jung - use Jung (ISOM)
		fr - An implementation of the Fruchtermon and Reingold force directed layout algorithm, that selects a random set of nodes (rather than all pairs)
	-m --format(default = auto) The format of the file, and desired graph representation
	Must be one of:
		auto - accepts: 
			.cnf - Load a DIMACS format file into a VIG and compute communities
			.sb - Load a graph representation from SB (JSON) file
		literal - accepts: 
			.cnf - Load a DIMACS format file into a LIG and compute communities
	-n --node-color(default = auto) node edge colouring implementation to use
	Must be one of: 
		auto - Nodes are blue
	-e --edge-color(default = auto) The edge colouring implementation to use
	Must be one of: 
		auto - Edges are coloured according to their community (or white for intercommunity)

##imp - View the graph and manually set the values of nodes to see how they propagate.   
	-f --file(default = null) The file (either .cnf or .sb)   
	Must be an existing file For which you have: read permissions   
	-u --url(default = null) A file URL (either .cnf or .sb)   
	-p --pattern(default = null) A list of regex expressions to group variables (not yet implemented)   
	-l --layout(default = f) The layout algorithm to use   
	Must be one of:    
		f - An implementation of the Fruchtermon and Reingold force directed layout algorithm   
		fgpu - A GPU implementation of the Fruchtermon and Reingold force directed layout algorithm   
		kk - An implementation of the Kamada-Kawai placement algorithm  
	Must be one of:
		auto - accepts: 
			.cnf - Load a DIMACS format file into a VIG allow manual variable setting 
	   
##evo - View the evolution of the structure of the graph, with other evolution properties presented.   
	-f --file(default = null) The file (either .cnf or .sb)
	Must be an existing file For which you have: read permissions
	-u --url(default = null) A file URL (either .cnf or .sb)
	-c --community(default = ol) The community detection algorithm
	Must be one of: 
		l - The Louvian community detection algorithm
		ol - The Online community detection algorithm
		cnm - The Clauset-Neuman-Moore community detection algorithm
	-p --pattern(default = null) A list of regex expressions to group variables (not yet implemented)
	-o --observers(default = null) A named evolution observer
	Must be one of: 
		Q - A graphical representation of the evolution of Q over the solution of the solver (based on the selected community metric)
		VSIDST - A graphical representation of the temporal locailty of the VSIDS decision heuristic
		VSIDSS - A graphical representation of the spacial locailty of the VSIDS decision heuristic
	-l --layout(default = f) The layout algorithm to use
	Must be one of: 
		f - An implementation of the Fruchtermon and Reingold force directed layout algorithm
		jung - use Jung (ISOM)
		fr - An implementation of the Fruchtermon and Reingold force directed layout algorithm, that selects a random set of nodes
		kk - An implementation of the Kamada-Kawai placement algorithm
		c - A basic layout algorithm, nodes are layed out within a community using the FR layout algorithm. The communities are then layed out in a circle, with those most connected next to each other.
		grid - A basic layout algorithm, nodes are layed out within a community in a grid pattern. The communities are then layed out on a grid
		gkk - A basic layout algorithm, nodes are layed out within a community using the KK algorithm. The communities are then layed out on a grid
	-m --format(default = auto) The format of the file, and desired graph representation
	Must be one of:
		auto - accepts: 
			.cnf - Load a DIMACS format file into a VIG and compute communities, then solve and display evolution
			.sb - Load a graph representation from SB (JSON) file
		literal - accepts: 
			.cnf - Load a DIMACS format file into a LIG and compute communities, then solve and display evolution
	-s --solver(default = solvers/minisat/minisat) The location of the modified solver
	Must be an existing file For which you have: execute permissions
	-e --edge-color(default = auto) The edge colouring implementation to use
	Must be one of: 
		auto - Edges are coloured according to their community (or white for intercommunity and red for conflict)
	-n --node-color(default = auto) The node colouring implementation to use
	Must be one of: 
		auto - Nodes are blue
		decisionTemp - Color the nodes between green and red based on number of decisions
		assignmentTemp - Color the nodes between green and red based on number of assignments

##evoData - Generate evolution data for a given SAT instance. Outputs data for each given `-o` to a new CSV file in the directory given by `-d`. Skips instances where the files already exist
	-w --window(default = 10) The number of decisions before re-computing Q
	Must be an integer
	-f --file(default = null) The file (.cnf)
	Must be an existing file For which you have: read permissions
	-d --directory(default = null) The output directory
	Must be an existing file 
	Must be a directory For which you have: write permissions
	-e --decisions(default = 10240) The number of decisions to solve until
	Must be an integer
	-p --pipe(default = solvers/piping/) The piping directory location
	Must be an existing directory 
	-s --solver(default = solvers/minisat/minisat) The location of the modified solver
	Must be an existing file For which you have: execute permissions
	-c --community(default = ol) The community detection algorithm
	Must be one of: 
		l - The Louvian community detection algorithm
		ol - The Online community detection algorithm
		cnm - The Clauset-Neuman-Moore community detection algorithm
	-o --observer(default = null) The name of the observer to use for the evolution (may list several)
	Must be one of: 
		Q - The evolution of Q over the solution of the solver (based on the selected community metric)
		VSIDST - The temporal locailty of the VSIDS decision heuristic
		VSIDSS - The spacial locailty of the VSIDS decision heuristic
	-m --format(default = auto) The format of the file, and desired graph representation
	Must be one of:
		auto - accepts: 
			.cnf - Load a DIMACS format file into a VIG and compute communities, then solve and display evolution
			.sb - Load a graph representation from SB (JSON) file
		literal - accepts: 
			.cnf - Load a DIMACS format file into a LIG and compute communities, then solve and display evolution

##generate - Generate static data for all files within the provided list, output to a csv.
	-f --file(default = null) The file containing a list of .cnf files
	Must be an existing file For which you have: read permissions
	-c --community(default = ol) The community detection algorithm
	Must be one of: 
		l - The Louvian community detection algorithm
		ol - The Online community detection algorithm
		cnm - The Clauset-Neuman-Moore community detection algorithm
	-o --output(default = null) The output CSV
	For which you have: write permissions
	-m --format(default = auto) The format of the file, and desired graph representation
	Must be one of:
		auto - accepts: 
			.cnf - Load a DIMACS format file into a VIG and compute communities, then solve and display evolution
			.sb - Load a graph representation from SB (JSON) file
		literal - accepts: 
			.cnf - Load a DIMACS format file into a LIG and compute communities, then solve and display evolution

##generateOne - Generate static data for the provided instance, output data as a csv line to a file in the provided directory (for parallel processing).
	-f --file(default = null) The file (.cnf)
	Must be an existing file For which you have: read permissions
	-d --directory(default = null) The output directory
	Must be an existing file 
	Must be a directoryFor which you have: write permissions
	-u --url(default = null) A file URL (.cnf)
	-c --community(default = ol) The community detection algorithm
	Must be one of: 
		l - The Louvian community detection algorithm
		ol - The Online community detection algorithm
		cnm - The Clauset-Neuman-Moore community detection algorithm
	-m --format(default = auto) The format of the file, and desired graph representation
	Must be one of:
		auto - accepts: 
			.cnf - Load a DIMACS format file into a VIG and compute communities, then solve and display evolution
			.sb - Load a graph representation from SB (JSON) file
		literal - accepts: 
			.cnf - Load a DIMACS format file into a LIG and compute communities, then solve and display evolution


#Extending SATGraf:
SATGraf may be extendid with trivial ease in three areas, and with slightly more involvement in a fourth.
The first three extensions can be done without access to the sourcecode if desired.

##Strucutral detection
At the moment various community structure mechanisms are the only ones supported, however any structure that assigns nodes to groups may also be used.

1. Create a class that implements `com.satlib.community.CommunityMetric`
   This interface has a single method: `getCommunities` which detects the community structure and assigns variables to groups.
2. Choose a name for the implementation and register it with `com.satlib.community.CommunityMetricFactory` using the `register(String name, String description, Class implementation)` method. 
3. your chosen named implementation is now available as one of the options of the `-c` command line option.

##Layout algorithm
At the moment only single level layout algorithms are supported.

1. Create a class that either implements `com.satgraf.graph.placer.Placer` interface, or extends the `com.satgraf.graph.placer.AbstractPlacer` class. 
   The `Placer` interface has only four methods, which are self explanatory. `getX(Node)`, `getY(Node)`, `getNodeAtXY(int x,int y)` and `init()` - this function is accessed only once, the layout algorithm should be located here.
2. Choose a name for the implementation and register it with `com.satgraf.graph.placer.PlacerFactory` using the `register(String name, String description, Class implementation)` method.
2. Your chosen named implementation is now available as one of the options of the `-l` command line option.

##Node and Edge colouring
The procedure is the same for nodes and edges, just replace `Node` with `Edge` where applicable.

1. Create a class the either implements `com.satgraf.graph.color.NodeColoring` or `com.satgraf.graph.color.EdgeColoring`.
2. Choose a name for the implementation and register it with `com.satgraf.graph.color.NodeColoringFactory` or `com.satgraf.graph.color.EdgeColoringFactory` respectively.
3. Your chosen named implementatin is now available as one of the options of the `-n` or `-e` command line option respectively.

##Supplementary evolution views
These views are observers of the evolution, and are notified whenever a variable or clause changes. They can show details about how different metrics change during the evolution.

1. Create a class that either implements either `com.satgraf.evolution.observers.VisualEvolutionObserver` or `com.satlib.evolution.observers.EvolutionObserver`. The only difference between these two interfaces is that one will be added as a view (to display graphical elements) and the other may only log to the console (or file).
2. Choose a name for the observer and register it with `com.satgraf.evolution.observers.EvolutionObserverFactory` using the `register(String name, String description, Class implementation)` method.
3. Your chosen named observer is now available as one of the options of the `-o` command line option.
4. (bonus) You can use non-visual evolution observers, that need not be called from the command line (e.g., `com.satgraf.evolution.UI.EvolutionDecisionTemperatureColoring`) by directly calling `com.satlib.evolution.observers.EvolutionObserverFactory.add(EvolutionObserver)`

##Different graph representations
at the moment, both the variable-incidence graph and literal-incidence graph are supported. However, other implementations may be useful. It is possible to implement new adapters for any graph representation in the following way:

1. Create a class that implements `com.satlib.graph.GraphFactory`.
    1. The `GraphFactory` class has five methods, which are mostly self explanatory `makeGraph(URL)`,`makeGraph(File)` and `getGraph()`. 
    2. `getNodeLists()` returns a `HashMap` of `String`=>`IntStringHashMap`, which are the variable id's and names. The string is the name of an arbitrary grouping.
    3. `getPatterns()` returns a `HashMap` of `String`=>`Pattern`, which is used to assign variables to groups based on their names.

2. Choose a name for your `GraphFactory` implementation, e.g. "CIG" (Clause-incidence graph). Also choose the file extensions that will be supported. For each file extension register the class with the `com.satlib.graph.GraphFactoryFactory` class using the `register(String name, String extension, Class implementation)` method. 
3. Your adapter is now available as one of the options of the `-m` command line option.
4. Your implementation must return either a `CommunityGraphFactory`, `EvolutioGraphFactory` or `ImplicationGraphFactory` depending on where it will be used.

#Implementing the SATGraf protocol in a solver
##If implementing your solver in C++ 

1. Include the Pipe class 
2. In your code, tell the Pipe class where your piped file will be. Ex: Pipe::getInstance()->openPipe("solvers/piping/myPipe.txt");
3. To inform SATgraf of variables changing state, send the following to the pipe: Pipe::getInstance()->printVar(const int id, int state, bool isDecisionVariable, int activity)
    1. id = the variable id
    2. state = the possible states are defined in Pipe.h and are VAR_ASSIGNED_TRUE, VAR_ASSIGNED_FALSE, VAR_UNASSIGNED
    3. isDecisionVariable(optional) = will highlight this variable in SATgraf. Does not neccessarily have to be a decision variable but can be used to highlight any variable if that is desired.
    4. activity(optional) = the associated activity of a variable. Refers to conflict activity and will highlight decision variables with an activity greater than 0 a different color than those that are 0
4. To inform SATgraf of the clauses being added or removed, do the following: Pipe::getInstance()->printClause(const string vars, int state)
    1. vars = a spaced string with all of the variables ids. Ex: 1 2 3 4 5
    2. state = the state of the clause. All of the states are defined in Pipe.h and are CLAUSE_ADDED, CLAUSE_REMOVED
5. (Optional) To inform SATgraf of the conflicts in the solving of the instance, do the following when a conflict arises Pipe::getInstance()->printConflict(). This can be done before and after a clause arises in order to see the state of the SAT instance at both of those times. Could be used to see any specific event within the solver.

##If implementing your solver in any other language

1. Ouputs are `\n` delimited.
2. There are three types of line
    1. clause lines begin with `c` followed by a space, followed by either a `+` to denote a clause added or `-` to denote a clause removed, followed with a space. This is followed by the space delimited list of the variables (not literals) involved in the clause.
       E.g. `c + 1 2 3` - this states that a clause with the variables 1, 2 and 3 is added.
    2. variable lines begin with a `v` followed by a space, followed by either a `p` to denote a propagated variable, or `d` to denote a decision variable. This is followed by a space, then either `0` to denote a false assignment or `1` to denote a true assignment or `2` to denote unassigned. This is followed by a space, then the variable.
       E.g. `v p 0 1` - this states that a the variable 1 is assigned false due to propagation.
    3. conflict lines begin with a `!` and is followed by a space, followed by the conflict count.
       E.g. `! 23` - denotes that 23 conflicts have occured.

