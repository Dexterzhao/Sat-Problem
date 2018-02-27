#include "SWcc.h"

#include <sys/times.h> //these two h files are for linux
#include <unistd.h>

void smooth_clause_weights()
{
	int i,clause;
	int new_total_weight=0;
	entry_ptr	ptr;
	
	for (i=1; i<=num_vars; i++) 
		dscore[i] = 0;
	
	//smooth clause dscore and update dscore of variables
	for (i = 0; i<num_clauses; i++)
	{
		clause_weights[i] = clause_weights[i]*p_scale+scale_ave;
		
		new_total_weight+=clause_weights[i];
		
		//update dscore of variables in this clause 
		if (sat_count[i]==0) 
		{
			ptr = clauses[i];
			while(ptr!=NULL)
			{
				dscore[ptr->var_num]+=clause_weights[i];
				ptr = ptr->next_in_clause;
			}
		}
		else  if(sat_count[i]==1)
			dscore[sat_var[i]]-=clause_weights[i];
	}
	
	ave_weight=new_total_weight/num_clauses;
}

void update_clause_weights()
{
	int i,clause;
	entry_ptr eptr;
	for(i=0; i < unsat_stack_fill_pointer; ++i)
	{
		clause = unsat_stack[i];
		clause_weights[clause]++;

		eptr = clauses[clause];
		
		while(eptr!=NULL)
		{
			dscore[eptr->var_num]++;
			
			if(dscore[eptr->var_num]>0 &&  conf_change[eptr->var_num]==1 && record_as_goodvar[eptr->var_num]==0 )
			{
				index_in_goodvar_stack[eptr->var_num] = goodvar_stack_fill_pointer;
				push(eptr->var_num,goodvar_stack);
				record_as_goodvar[eptr->var_num]=1;
			}

			eptr = eptr->next_in_clause;
		}
	}
	
	delta_total_weight+=unsat_stack_fill_pointer;
	if(delta_total_weight>=num_clauses)
	{
		ave_weight+=1;
		delta_total_weight -= num_clauses;
		
		//smooth weights
		if(ave_weight>threshold)
			smooth_clause_weights();
	}

}



//pick a var of an unsat clause 
int pick_var()
{
	int             k,i;
	int             best_var;

	int				flipvar;
	entry_ptr		eptr;

	int				oldest_stamp;

	if(goodvar_stack_fill_pointer>0)
	{
		best_var = goodvar_stack[0];
		
		for(i=1;i<goodvar_stack_fill_pointer;++i)
		{
			k = goodvar_stack[i];
			if (dscore[k] > dscore[best_var]) 
			{
				best_var = k;
			}
			else if (dscore[k]==dscore[best_var] && time_stamp[k]<time_stamp[best_var] )//prefer older var to break the tie
			{
				best_var = k;
			}
		}
		
		return best_var;
	}

	else 
	{
		update_clause_weights();

		oldest_stamp = max_flips;
		//pick a random unsat clause
		eptr = clauses[unsat_stack[rng.next(unsat_stack_fill_pointer)]];
		while(eptr!=NULL)
		{
			k = eptr->var_num;
			if(time_stamp[k]<oldest_stamp)
			{
				oldest_stamp = time_stamp[k];
				flipvar = k;
			}
			eptr = eptr->next_in_clause;
		}
		return flipvar;
	}

}


int step;
void local_search(int max_flips)
{
	int flipvar;
	int k;
     
	for (step = 0; step<max_flips; step++)
	{
		//find the solution
		if(unsat_stack_fill_pointer==0){
			for (k = 1; k <= num_vars; k++) 
				best_soln[k] = cur_soln[k];
			break;
		}

		flipvar = pick_var();

		flip(flipvar);
		time_stamp[flipvar] = step;
	}
}



int main(int argc, char* argv[])
{
     int             seed;
     
	 struct tms start, stop;

	 build_instance(argv[1]);
     
     sscanf(argv[2],"%d",&seed);
	 //sscanf(argv[3],"%d",&max_flips);
	 //sscanf(argv[4],"%d",&threshold);
	 
	 scale_ave=(threshold+1)*q_scale;//when smoothing, ave_weight=threshold+1.
	 
	 
	 //printf("%d ", seed);
	 printf("c this is swcc version 1.0 \n");

	 rng.seed(seed);
	 
	 times(&start);

     //max_tries = 1;
     //max_flips = 1000000000;

	 //for (i = 1; i <= max_tries; i++) 
	 //{
		 init();
	 
		 local_search(max_flips);

	/*	 total_step += step;
		 if (best_unsat_size == 0)  
			 break;
	 }*/


	  times(&stop);
	  double comp_time = double(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);

     //print out information about the solution.
	 if(unsat_stack_fill_pointer==0){
		 if(verify_sol()==1)
		 {
			 //printf("sat %d %lf \n",step,comp_time);
			 printf("s SATISFIABLE\n");
			 print_best_solution();

			 printf("c searchSteps = %d\n", step); 
			 printf("c solveTime = %lf\n",comp_time);
		 }
	 }
	 else printf("s unkown %d %lf \n",step,comp_time);
	 
	 
	 free_memory();

     return 0;
}
