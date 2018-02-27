/************************************************
** Date:   2011.5.1 
** SWcc (Smoothed Weighting with Configuration Checking) 
** is a Local Search SAT solver
** Author: Shaowei Cai, shaowei_cai@126.com    
**		   School of EECS, Peking University   
**		   Beijing, China                      
**             
** Date:   2011.5.15
** SWcc : tidy the codes, and add the free_memory() function
**         to free the memory by malloc function.     
**       
** Date:   2011.5.22
** SWcc : optimize the smooth_clause_weights() funtion. 
**        before this version, the funtion compute dscore by a loop on 
**        each variable, each variable takes a loop on all the clauses
**        it appears; in this version, we compute dscore when we smooth 
**        the clause weight. In detail, only when the clause is unsat or
**		  has only one true literal (we record the variable of the true 
**        literal as sat_var[i] for clause i) we update dscore.                        
************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include "mersenne.cc" 

/* limits on the size of the problem. */
#define MAX_VARS    100000
#define MAX_CLAUSES 5000000

#define pop_top(stack) --stack ## _fill_pointer
#define pop(stack) stack[--stack ## _fill_pointer]
#define push(item, stack) stack[stack ## _fill_pointer++] = item


Mersenne rng;


// Define a record type for the entries in the SAT problem data structure.
typedef struct entry* entry_ptr;

struct entry {
     int             clause_num;
     int             var_num;		//variable num, begin with 1
     int             sense;			//is 1 for true literals, 0 for false literals.
     entry_ptr       next_in_var_pos;	//point to the next entry with this variable.
	 entry_ptr       next_in_var_neg;
     entry_ptr       next_in_clause;//point to the next entry in the current clause.
};


/*parameters of the instance*/
int             num_vars;		
int             num_clauses;	

/* Information about the variables. */				
entry_ptr       vars_pos[MAX_VARS];					
entry_ptr       vars_neg[MAX_VARS];					

int             dscore[MAX_VARS];				
int				time_stamp[MAX_VARS];
int				conf_change[MAX_VARS];
int*			var_neighbor[MAX_VARS];
int				var_neighbor_count[MAX_VARS];


/* Information about the clauses */
entry_ptr       clauses[MAX_CLAUSES];			
int             clause_weights[MAX_CLAUSES];	
int             clause_lit_count[MAX_CLAUSES];	
int             sat_count[MAX_CLAUSES];			
int				sat_var[MAX_CLAUSES];			


/* smooth */
int				ave_weight=1;
int				delta_total_weight=0;
int				threshold=300;
float			p_scale=0.3;//w=w*p+ave*(1-p)
float			q_scale=0.7;//q=1-p 
int				scale_ave;//scale_ave==ave_weight*q_scale


//unsat clauses stack
int				unsat_stack[MAX_CLAUSES];		//store the unsat clause number
int				unsat_stack_fill_pointer;
int				index_in_unsat_stack[MAX_CLAUSES];//which position is a clause in the unsat_stack


//candidate variable to flip (dscore>0 and confchange=1)
int				goodvar_stack[MAX_VARS];		
int				goodvar_stack_fill_pointer;
int				index_in_goodvar_stack[MAX_VARS];
int				record_as_goodvar[MAX_VARS];		// has been recorded in the stack or not


/* Information about solution */
int             cur_soln[MAX_VARS];	//the current solution, with 1's for True variables, and 0's for False variables
int             best_soln[MAX_VARS];


//int             max_tries;
int            max_flips = 2000000000;

//the funcions
void build_instance(char *filename);
void init();
void remove_unsat(int clause);
void add_unsat(int clause);
void flip(int var);

/*
 * Read in the problem.
 */
void build_instance(char *filename)
{
	FILE            *fp;
	char            line[100];
	char   			*tempstr;
	char            tempstr1[10];
	char            tempstr2[10];
	int				lit;
	int             temp;
	int             i;
	entry_ptr       ptr;

	fp = fopen(filename, "r");
	if(fp==NULL) 
	{
		printf("Cannot find the input file. Make sure the filename is correct.\n");
		exit(0);
	}

	tempstr=fgets(line, 100, fp);
	while (line[0] != 'p')
		tempstr=fgets(line, 100, fp);
	sscanf(line, "%s %s %d %d", tempstr1, tempstr2, &num_vars, &num_clauses);

	//Initialize the arrays of pointers.
	for (i = 1; i <= num_vars; i++) 
	{
		vars_pos[i] = NULL;
		vars_neg[i] = NULL;
	}
	for (i = 0; i < num_clauses; i++) 
	{
		clauses[i] = NULL;
		clause_lit_count[i] = 0;
	}

	//Now, read in the clauses, one at a time.
	for (i = 0; i < num_clauses; i++) 
	{
		temp = fscanf(fp, "%d", &lit);
		while (lit != 0) {
			//each clause cannot contain the same literal (u u) or the oposit literals(u -u). 

			//Allocate an entry for this literal.
			ptr = (entry_ptr) malloc(sizeof(struct entry));
			ptr->clause_num = i;
			ptr->var_num = abs(lit);
			if (lit > 0) ptr->sense = 1;
			else ptr->sense = 0;

			//Insert to the clause at the head
			ptr->next_in_clause = clauses[i];
			clauses[i] = ptr;
			clause_lit_count[i] = clause_lit_count[i] + 1;

			//Insert to the var list at the head of the corresponding literal list of the var.
			if(lit>0)
			{
				ptr->next_in_var_pos = vars_pos[ptr->var_num];
				vars_pos[ptr->var_num] = ptr;
			}
			else
			{
				ptr->next_in_var_neg = vars_neg[ptr->var_num];
				vars_neg[ptr->var_num] = ptr;
			}
			
			//Finally, get the next number out of the file.
			temp = fscanf(fp, "%d", &lit);
		}
	}
}

void build_neighbor_relation()
{
	int		neighbor_flag[MAX_VARS];
	int		i,j,count;
	entry_ptr	ptr, ptr2;
	int			clause;

	for(i=1; i<=num_vars; ++i)
	{
		var_neighbor_count[i] = 0;

		for(j=1; j<=num_vars; ++j)
			neighbor_flag[j] = 0;
		neighbor_flag[i] = 1;

		
		ptr = vars_pos[i];
		while (ptr != NULL)
		{
			clause = ptr->clause_num;

			ptr2 = clauses[clause];

			while (ptr2 != NULL) 
			{
				if(neighbor_flag[ptr2->var_num]==0)
				{
					var_neighbor_count[i]++;
					neighbor_flag[ptr2->var_num] = 1;
				}
				ptr2 = ptr2->next_in_clause;
			}

			ptr = ptr->next_in_var_pos;
		}
		ptr = vars_neg[i];
		while (ptr != NULL)
		{
			clause = ptr->clause_num;

			ptr2 = clauses[clause];

			while (ptr2 != NULL) 
			{
				if(neighbor_flag[ptr2->var_num]==0)
				{
					var_neighbor_count[i]++;
					neighbor_flag[ptr2->var_num] = 1;
				}
				ptr2 = ptr2->next_in_clause;
			}

			ptr = ptr->next_in_var_neg;
		}
		neighbor_flag[i] = 0;
 
		var_neighbor[i] = (int*)malloc(var_neighbor_count[i]*sizeof(int));

		count = 0;
		for(j=1; j<=num_vars; ++j)
		{
			if(neighbor_flag[j]==1)
			{
				var_neighbor[i][count] = j;
				count++;
			}
		}

	}
}


void free_memory()
{
	int i;
	entry_ptr eptr,next;
	for (i = 0; i < num_clauses; i++) 
	{
		eptr = clauses[i];
		while(eptr!=NULL)
		{
			next = eptr->next_in_clause;
			
			free(eptr);

			eptr = next;
		}
	}
	
	for(i=1; i<=num_vars; ++i)
	{
		free(var_neighbor[i]);
	}
	
}


inline
void unsat(int clause)
{
	index_in_unsat_stack[clause] = unsat_stack_fill_pointer;
	push(clause,unsat_stack);
}


inline
void sat(int clause)
{
	int index,last_unsat_clause;

	/*if(index == unsat_stack_fill_pointer-1)
		pop_top(unsat_stack);
	else{*/
		//since the clause is satisfied, its position can be reused to store the last_unsat_clause
		last_unsat_clause = pop(unsat_stack);
		index = index_in_unsat_stack[clause];
		unsat_stack[index] = last_unsat_clause;
		index_in_unsat_stack[last_unsat_clause] = index;
	//}
}

//initiation of the algorithm

void init()
{
	int v,c;
	entry_ptr	ptr;
	int			clause;
	
	//Initialize edge weights
	for (c = num_clauses; c>=0; c--)
		clause_weights[c] = 1;

	//init unsat_stack
	unsat_stack_fill_pointer = 0;

	//build neighbor relation
	build_neighbor_relation();

	//init solution
	for (v = 1; v <= num_vars; v++) {

		if(rng.next(2)==1) cur_soln[v] = 1;
		else cur_soln[v] = 0;

		time_stamp[v] = 0;
		conf_change[v] = 1;
	}
	time_stamp[0] = 0;

	/* figure out sat_count, and init unsat_stack */
	for (c=0; c<num_clauses; c++) 
	{
		sat_count[c] = 0;
		ptr = clauses[c];
		while (ptr != NULL)
		{
			if (cur_soln[ptr->var_num] == ptr->sense)
			{
				sat_count[c]++;
				sat_var[c] = ptr->var_num;	
			}
			ptr = ptr->next_in_clause;
		}
		if (sat_count[c] == 0) 
			unsat(c);
	}

	/*figure out var dscore*/
	for (v=1; v<=num_vars; v++) 
	{
		dscore[v] = 0;
		ptr = vars_pos[v];
		while (ptr != NULL)
		{
			clause = ptr->clause_num;

			if (sat_count[clause]==0) dscore[v]++;
			else if (sat_count[clause]==1 && ptr->sense==cur_soln[v]) dscore[v]--;
				
			ptr = ptr->next_in_var_pos;
		}
		ptr = vars_neg[v];
		while (ptr != NULL)
		{
			clause = ptr->clause_num;

			if (sat_count[clause]==0) dscore[v]++;
			else if (sat_count[clause]==1 && ptr->sense==cur_soln[v]) dscore[v]--;
				
			ptr = ptr->next_in_var_neg;
		}
	}
	dscore[0]=0;
		
	//init goodvars stack
	goodvar_stack_fill_pointer = 0;
	for (v=1; v<=num_vars; v++) 
	{
		if(dscore[v]>0 && conf_change[v]==1)
		{
			index_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
			push(v,goodvar_stack);
			record_as_goodvar[v]=1;
		}
		else
			record_as_goodvar[v]=0;
	}

	 //threshold  = sqrt((float)num_vars)*20;
}



void flip_to_pos(int flipvar)
 {
	entry_ptr	ptr,ptr2;
	int			clause;

	 //update related clauses and neighbor vars
	ptr = vars_neg[flipvar];
	while (ptr != NULL)
	{
		clause = ptr->clause_num;

		--sat_count[clause];
		if (sat_count[clause] == 0) //sat_count from 1 to 0
		{
			ptr2 = clauses[clause];
			while (ptr2 != NULL) 
			{
				dscore[ptr2->var_num] += clause_weights[clause];
				
				ptr2 = ptr2->next_in_clause;
			}
			unsat(clause);
		}
		else if (sat_count[clause] == 1) //sat_count from 2 to 1
		{
			ptr2 = clauses[clause];
			while (ptr2 != NULL) 
			{
				if (ptr2->sense == cur_soln[ptr2->var_num]) 
				{
					dscore[ptr2->var_num] -= clause_weights[clause];
					sat_var[clause] = ptr2->var_num;
					break;
				}
				ptr2 = ptr2->next_in_clause;
			}
		}

		ptr = ptr->next_in_var_neg;
	}

	ptr = vars_pos[flipvar];
	while (ptr != NULL)
	{
		clause = ptr->clause_num;

		++sat_count[clause];
		if (sat_count[clause] == 1) // sat_count from 0 to 1
		{
			sat_var[clause] = flipvar;//record the only true lit's var

			ptr2 = clauses[clause];
			while (ptr2 != NULL) 
			{
				dscore[ptr2->var_num] -= clause_weights[clause];
				ptr2 = ptr2->next_in_clause;
			}

			sat(clause);
		}
		else if (sat_count[clause] == 2) //sat_count from 1 to 2
		{
			dscore[sat_var[clause]] += clause_weights[clause];
		}

		ptr = ptr->next_in_var_pos;
	}

 }

 void flip_to_neg(int flipvar)
 {
	entry_ptr	ptr,ptr2;
	int			clause;

	//update related clauses and neighbor vars
	ptr = vars_pos[flipvar];
	while (ptr != NULL)
	{
		clause = ptr->clause_num;

		--sat_count[clause];
		if (sat_count[clause] == 0) //sat_count from 1 to 0
		{
			ptr2 = clauses[clause];
			while (ptr2 != NULL) 
			{
				dscore[ptr2->var_num] += clause_weights[clause];
				ptr2 = ptr2->next_in_clause;
			}
			unsat(clause);
		}
		else if (sat_count[clause] == 1) //sat_count from 2 to 1
		{
			ptr2 = clauses[clause];
			while (ptr2 != NULL) 
			{
				if (ptr2->sense == cur_soln[ptr2->var_num]) 
				{
					dscore[ptr2->var_num] -= clause_weights[clause];
					sat_var[clause] = ptr2->var_num;
					break;
				}
				ptr2 = ptr2->next_in_clause;
			}
		}

		ptr = ptr->next_in_var_pos;
	}

	ptr = vars_neg[flipvar];
	while (ptr != NULL)
	{
		clause = ptr->clause_num;

		++sat_count[clause];
		if (sat_count[clause] == 1) // sat_count from 0 to 1
		{
			sat_var[clause] = flipvar;//record the only true lit's var

			ptr2 = clauses[clause];
			while (ptr2 != NULL) 
			{
				dscore[ptr2->var_num] -= clause_weights[clause];
				ptr2 = ptr2->next_in_clause;
			}

			sat(clause);
		}
		else if (sat_count[clause] == 2) //sat_count from 1 to 2
		{
			dscore[sat_var[clause]] += clause_weights[clause];
		}

		ptr = ptr->next_in_var_neg;
	}
	
 }
 
 
//flip a var, and do the neccessary updating
void flip(int flipvar)
{
	int i,v;
	int index,last_goodvar;
	//int tmp_stack_len;
	int org_flipvar_dscore = dscore[flipvar];
	cur_soln[flipvar] = 1 - cur_soln[flipvar];

	if(cur_soln[flipvar]==1)
		flip_to_pos(flipvar);
	else flip_to_neg(flipvar);

	dscore[flipvar] = -org_flipvar_dscore;
	conf_change[flipvar] = 0;
	
	//remove the vars no longer goodvar in goodvar stack 
	for(index=goodvar_stack_fill_pointer-1; index>=0; index--)
	{
	    v = goodvar_stack[index];
		if(dscore[v]<=0)
		{
			last_goodvar = pop(goodvar_stack);
			//index = index_in_goodvar_stack[v];
			goodvar_stack[index] = last_goodvar;
			index_in_goodvar_stack[last_goodvar] = index;
			
			record_as_goodvar[v]=0;
		}	
	}

	//update all flipvar's neighbor's conf_change to be 1, add goodvar
	for(i=0; i<var_neighbor_count[flipvar]; ++i)
	{
		v = var_neighbor[flipvar][i];
		conf_change[v] = 1;
		
		if(dscore[v]>0 && record_as_goodvar[v]==0) 
		{
			index_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
			push(v,goodvar_stack);
			record_as_goodvar[v]=1;
		}
		
	}
 
}



void print_best_solution()
{
     int             i;

	 printf("v ");
     for (i=1; i<=num_vars; i++) {
		 if(best_soln[i]==0)printf("-");
       printf("%d ",i);
       
       if(i%10==0) printf("\nv ");
     }
	 printf("0\n");
}

int verify_sol()
{
	int i; int flag;
	
	for (i = 0; i <= num_clauses - 1; i++) 
	{
		entry_ptr ptr2 = clauses[i];
		flag = 0;
		while (ptr2 != ((entry_ptr) NULL)) {
			if (best_soln[ptr2->var_num] == ptr2->sense) {flag = 1; break;}
			
			ptr2 = ptr2->next_in_clause;
		}

		if(flag ==0){//output the clause unsatisfied by the solution
			printf("clause %d is not satisfied.\n", i);

			ptr2 = clauses[i];
			while (ptr2 != ((entry_ptr) NULL)) {

				if(ptr2->sense==0)printf("-");
				printf("%d ",ptr2->var_num);
				ptr2 = ptr2->next_in_clause;
			};
			printf("\n");

			ptr2 = clauses[i];
			while (ptr2 != ((entry_ptr) NULL)) {

				printf("%d ",best_soln[ptr2->var_num]);
				ptr2 = ptr2->next_in_clause;
			};
			printf("\n");

			return 0;
		}
	}
	return 1;
}
