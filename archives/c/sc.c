#include <stdio.h>
#include <conio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

#define REGION_MAX 100
#define	HD "  Node  Pred  TS  NOS     Flow      Intercept     Slope       Price\n"

struct node_data
{ int     node_id;
  float	  intercept;
  float	  slope;
  float	  price;
	float   excess;
	float   flow;
  char    trade_status;
	int	    nos;
  float	  sos;
  struct  node_data *pred;
  struct  node_data *thread;
} ;


struct	node_data  *top,*root,*last_root,*current,*holder,*left,*right,
                   *d2_pointer,*in_tree,*out_tree,*export_to,*import_from,
                   *order[(REGION_MAX+1)];

char    filename[8],d_filename[11],c_filename[11],o_filename[11],line[80];
int     i,j,k,n,choice,sort,skip,
        iteration_counter[REGION_MAX];
float   delta,
        start_time,sort_time,run_time,total_time,
        cost[REGION_MAX][REGION_MAX];
FILE    *demandfile,*costfile,*dev;


void  linkfloat(float *f1) {float f2 = *f1; linkfloat(&f2);}
      /* tricks linkage of floating point formats */


void  load_data()
{ top = (struct node_data*) malloc(sizeof(struct node_data));
  top->node_id = 999;
  top->slope = 0.0;

  while (!feof(demandfile))
  { root = (struct node_data*) malloc(sizeof(struct node_data));
    fgets(line, 80, demandfile);
    sscanf(line,"%d %f %f",&root->node_id,&root->intercept,&root->slope);
    root->price = root->intercept/root->slope;
    root->excess = 0.0;
    root->trade_status = 0;
    root->pred = NULL;
    root->nos = 1;
    root->sos = root->slope;
    root->flow = 0.0;
    root->thread = NULL;
    order[i++] = root;
  }
  fclose(demandfile);
  n = --i;
  order[n] = top;

  for (i = 0; i < n; i++)
    for (j = 0; j < n; j++)
      fscanf(costfile,"%f",&cost[i][j]);
  fclose(costfile);
}


void  insertion_sort()
{ float   t;
  struct  node_data   *u;

  for (i = (n - 1); i >= 0; i--)
  { j = i;
    t = order[i]->slope;
    u = order[i];
    while (t < order[j+1]->slope)
      order[j++] = order[j+1];
    order[j] = u;
} }


float market_clear()
{ float   largest = 0.0;

  current = root;
  while (current->pred != NULL)
    current = current->pred;
  holder = current;
  do
  { current->excess = current->intercept - current->slope * current->price;
    if (current->pred != NULL)
      current->pred->excess += current->flow;
    current->excess -= current->flow;
    current = current->thread;
  }
  while (current != holder);
  do
  { if (fabs(current->excess) > largest)
      largest = current->excess;
    current = current->thread;
  }
  while (current != holder);
  return largest;
}


void  forest_status(char  from_where[80])
{ fprintf(dev,"\nForest status %s:\n",from_where);
  current = root;
  holder = root;
  fprintf(dev,HD);
  do
  { fprintf(dev,"   %3d",current->node_id);
    if (current->pred != NULL)
      fprintf(dev,"   %3d",current->pred->node_id);
    else fprintf(dev,"  NULL");
    fprintf(dev,"  %2d  %2d  %10.5f  %10.5f  %10.5f  %10.5f\n",
            current->trade_status,current->nos,current->flow,
            current->intercept,current->slope,current->price);
    current = current->thread;
  }
  while (current != holder);
}


void  forest_update(struct  node_data  *attach_to, struct node_data  *attacher)
{ int     i;
  struct  node_data  *path_leader,*path_mid,*path_follower;

  path_follower = attacher;
  path_mid = attacher;
  path_leader = path_mid->pred;
  right = attacher; left = holder = NULL;
  for (i = 1; i < path_mid->nos; i++)
    right = right->thread;
  while (path_leader != NULL)
  { left = path_leader;
    while (left->thread != path_mid)
    { left = left->thread;
      path_leader->nos -= left->nos;
      path_leader->sos -= left->sos;
      current = left;
      for (i = 1; i < current->nos; i++)
        left = left->thread;
    }
    holder = right->thread;
    right->thread = path_leader;
    left->thread = holder;
    path_follower = path_mid;
    path_mid = path_leader;
    path_leader = path_mid->pred;
    path_mid->pred = path_follower;
    path_mid->nos = attach_to->nos - path_mid->nos;
    path_mid->sos = attach_to->sos - attach_to->slope
                    - (path_mid->sos - path_mid->slope);
    right = left;
    while (right->thread->pred == path_mid)
    { right = right->thread;
      path_mid->nos += right->nos;
      path_mid->sos += right->sos;
      current = right;
      for (i = 1; i < current->nos; i++)
        right = right->thread;
    }
  }
  current = last_root;
	if (attacher != last_root)
		while (current != attacher)
    { current->flow = - current->pred->flow;
      current = current->pred;
    }
  attacher->pred = attach_to;
  attacher->trade_status = -attach_to->trade_status;
  attacher->nos = attach_to->nos - 1;
  attacher->sos = attach_to->sos - attach_to->slope;
  attacher->flow = 0.0;
}


void  split()
{ int     i;

  right = d2_pointer;
  left = d2_pointer->pred;
  current = left;
  while (left->thread != d2_pointer)
    left = left->thread;
  current->nos -= d2_pointer->nos;
  current->sos -= d2_pointer->sos;
  d2_pointer->flow = 0.0;
  if (d2_pointer->nos == 1)
    d2_pointer->trade_status = 0;
  d2_pointer->pred = NULL;
  for (i = 1; i < d2_pointer->nos; i++)
    right = right->thread;
  left->thread = right->thread;
  while (left->thread->pred != NULL)
    left = left->thread;
  holder = left->thread;
  left->thread = d2_pointer;
  right->thread = holder;
  current = current->pred;
  while (current != NULL)
  { current->nos -= d2_pointer->nos;
    current->sos -= d2_pointer->sos;
    current = current->pred;
  }
}


void  splice()
{ int     i,nos_holder;
  float   sos_holder;
  struct  node_data  *marker_1,*marker_2;

  current = in_tree;
  for (i = 1; i < in_tree->nos; i++)
    current = current->thread;
  marker_1 = current->thread;
  last_root = out_tree;
  while (last_root->pred != NULL)
    last_root = last_root->pred;
  marker_2 = in_tree;
  while (marker_2->thread != last_root)
    marker_2 = marker_2->thread;
  current->thread = out_tree;
  nos_holder = in_tree->nos - 1;
  sos_holder = in_tree->sos - in_tree->slope;
  in_tree->nos = last_root->nos + 1;
  in_tree->sos = last_root->sos + in_tree->slope;
  forest_update(in_tree,out_tree);
	if (marker_1 != last_root)
  { holder = right->thread;
    right->thread = marker_1;
    marker_2->thread = holder;
  }
  in_tree->nos += nos_holder;
  in_tree->sos += sos_holder;
  current = in_tree->pred;
  while (current != NULL)
  { current->nos += out_tree->nos;
    current->sos += out_tree->sos;
    current = current->pred;
  }
}


void  price_and_flow_update(struct  node_data  *marker)
{ do
  { left = left->thread;
    left->price += delta;
    left->excess = left->intercept - left->slope * left->price;
  }
  while (left->nos != 1);
    left->flow = left->excess;
  left->pred->excess += left->flow;
  left->excess = 0.0;
  if (left->thread->pred == left->pred)
    price_and_flow_update(left);
  else right = left;

  while ((left != marker->pred) && (left != NULL))
  { left = left->pred;
    if (left == right->thread->pred)
      {	left = right;
        price_and_flow_update(right->thread->pred->thread);
      }
    else if (left != root)
    { left->flow = left->excess;
      left->pred->excess += left->flow;
      left->excess = 0.0;
} } }


void  ratio()
{ int     i,left_node_id;
  float   d1,d2,d2_temp,d3,dif_temp,dif;
  struct  node_data  *in_tree_temp,*out_tree_temp;

  if (root->trade_status == -1)
  { do
    { iteration_counter[k] = iteration_counter[k] + 1;
      d1 = root->excess/root->sos;
      d2_temp = d2 = d3 = -1E6;
      d2_pointer = in_tree_temp = in_tree = out_tree_temp = out_tree = NULL;

      current = root;
        while (current->thread->pred != NULL)
      current = current->thread;
      left = root;

      for (i = 0; i < root->nos; i++)
      { if (left->trade_status == -1)
        { if (i != 0)
            if ((d2_temp = left->flow/left->sos) > d2)
              d2 = d2_temp, d2_pointer = left;

          if (current->thread != root)
          { dif = dif_temp = -1E6;
            left_node_id = left->node_id;
            right = current->thread;
            while (right != root)
            { if (right->trade_status != -1)
                if ((dif_temp = right->price
                                - cost[left_node_id][right->node_id]) > dif)
                  dif = dif_temp, in_tree_temp = left, out_tree_temp = right;
              right = right->thread;
            }
            dif -= left->price;
            if (dif > d3)
              d3 = dif, in_tree = in_tree_temp, out_tree = out_tree_temp;
        } }
        left = left->thread;
      }

      if ((d2 >= d1) && (d2 >= d3))
      { delta = d2;
        root->price += delta;
        root->excess = root->intercept - root->slope * root->price;
        left = root;
        right = NULL;
        price_and_flow_update(left->thread);
        split();
      }
      else if ((d3 >= d1) && (d3 >= d2))
      { delta = d3;
        root->price += delta;
        root->excess = root->intercept - root->slope * root->price;
        left = root;
        right = NULL;
        price_and_flow_update(left->thread);
        splice();
    } }
    while ((d1 < d2) || (d1 < d3));
  }
  else
  { do
    { iteration_counter[k] = iteration_counter[k] + 1;
      d1 = root->excess/root->sos;
      d2_temp = d2 = d3 = 1E6;
      d2_pointer = in_tree_temp = in_tree = out_tree_temp = out_tree = NULL;

      current = root;
      while (current->thread->pred != NULL)
        current = current->thread;
      left = root;

      for (i = 0; i < root->nos; i++)
      { if (left->trade_status == 1)
        { if (i != 0)
            if ((d2_temp = left->flow/left->sos) < d2)
              d2 = d2_temp, d2_pointer = left;

          if (current->thread != root)
          { dif = dif_temp = 1E6;
            left_node_id = left->node_id;
            right = current->thread;
            while (right != root)
            { if (right->trade_status != 1)
                if ((dif_temp = right->price
                                + cost[right->node_id][left_node_id]) < dif)
                  dif = dif_temp, in_tree_temp = left, out_tree_temp = right;
              right = right->thread;
            }
            dif -= left->price;
            if (dif < d3)
              d3 = dif, in_tree = in_tree_temp, out_tree = out_tree_temp;
        } }
        left = left->thread;
      }

      if ((d2 <= d1) && (d2 <= d3))
      { delta = d2;
        root->price += delta;
        root->excess = root->intercept - root->slope * root->price;
        left = root;
        right = NULL;
        price_and_flow_update(left->thread);
        split();
      }
      else if ((d3 <= d1) && (d3 <= d2))
      { delta = d3;
        root->price += delta;
        root->excess = root->intercept - root->slope * root->price;
        left = root;
        right = NULL;
        price_and_flow_update(left->thread);
        splice();
    } }
    while ((d1 > d2) || (d1 > d3));
  }
  delta = d1;
  root->price += delta;
  root->excess = root->intercept - root->slope * root->price;
  left = root;
  right = NULL;
  price_and_flow_update(left->thread);
}


void  main_loop()
{ float   L,U,L_temp,U_temp;

  root = order[0];
  root->thread = root;
  iteration_counter[0] = 0;

  for (k = 1; k < n; k++)
  { start_time = clock();
    current = root;
    root = order[k];
    iteration_counter[k] = 0;
    export_to = import_from = NULL;
    L = L_temp = -1E6;
    U = U_temp =  1E6;
    holder = current;
    do
    { if (current->trade_status != 1)
        if ((U_temp = current->price
                      + cost[current->node_id][root->node_id]) < U)
          U = U_temp, import_from = current;
      if (current->trade_status != -1)
        if ((L_temp = current->price
                      - cost[root->node_id][current->node_id]) > L)
          L = L_temp, export_to = current;
      current = current->thread;
    }
    while (current != holder);

    if (root->price > U)
    { import_from->trade_status = -1;
      last_root = import_from;
      while (last_root->pred != NULL)
        last_root = last_root->pred;
      root->price = U;
      root->excess = root->intercept - root->slope * root->price;
      root->trade_status = 1;
      root->nos = last_root->nos + 1;
      root->sos = last_root->sos + root->slope;
      root->thread = import_from;
      forest_update(root,import_from);
      if (right->thread != root)
      { while (right->thread != last_root)
          right = right->thread;
        right->thread = root;
      }
      ratio();
    }
    else if (root->price < L)
    { export_to->trade_status = 1;
      last_root = export_to;
      while (last_root->pred != NULL)
        last_root = last_root->pred;
      root->price = L;
      root->excess = root->intercept - root->slope * root->price;
      root->trade_status = -1;
      root->nos = last_root->nos + 1;
      root->sos = last_root->sos + root->slope;
      root->thread = export_to;
      forest_update(root,export_to);
      if (right->thread != root)
      { while (right->thread != last_root)
          right = right->thread;
        right->thread = root;
      }
      ratio();
    }
    else
    { root->trade_status = 0;
      root->thread = current;
      do
        current = current->thread;
      while (current->thread != holder);
      current->thread = root;
    }
    run_time = run_time + clock() - start_time;
  }
}


main()
{ clrscr();
  puts("The expanding equilibrium algorithm for single commodity problems");
  puts("Copyright 1989 Eric S. Theise.  All rights reserved.");
  do
  { skip = 'y';
    printf("\nWhat is the name of the problem to be solved?  ");
    scanf("%s",filename);
    strcpy(d_filename,filename);
    strcpy(c_filename,filename);
    if ((demandfile = fopen(strcat(d_filename,".DEM"),"rt")) == NULL)
    { printf("  %s is not on this disk\n",d_filename);
      skip = 'n';
    }
    if ((costfile = fopen(strcat(c_filename,".Cij"),"rt")) == NULL)
    { printf("  %s is not on this disk\n",c_filename);
      skip = 'n';
  } }
  while (skip != 'y');

  puts("\nWhere should output be sent:");
  puts("     screen  (s)?");
  puts("     printer (p)?");
  printf("     or file (f)?  ");
  choice = getche(); puts("\n");
  switch (choice)
  { case 'p':
      dev = stdprn;
      skip = 'y';
      break;
    case 'f':
      strcpy(o_filename,filename);
      dev = fopen(strcat(o_filename,".out"),"wt");
      printf("Output will be sent to file %s\n",o_filename);
      skip = 'y';
      break;
    default:
      dev = stdout;
      skip = 'n';
      break;
  }
  printf("Do you want regions sorted by excess demand slopes? (y/n) ");
  sort = getche();
  printf("\n\nWorking ...\n");

  load_data();
  if (sort != 'n')
  { sort_time = clock();
    insertion_sort();
    sort_time = clock() - sort_time;
  }
  main_loop();
  if (skip == 'y')
    fprintf(dev,"The expanding equilibrium algorithm on %s\n\n",filename);
  forest_status("at final solution"); fputs("\n",dev);
  if (skip == 'n')
  { printf("Any key to continue ... ");
    choice = getch(); puts("\n");
  }
  for (j = 0; j < n; j++)
    fprintf(dev,"Bringing node %3d into equilibrium required %2d ratio tests\n"
               ,order[j]->node_id,iteration_counter[j]);
  fputs("\n",dev);
  fprintf(dev,"Insertion sort time:        ");
  if (sort == 'y')
    fprintf(dev,"%10.2f seconds\n",sort_time/CLK_TCK);
  else fprintf(dev,"sort not performed\n");
  fprintf(dev,"Expanding equilibrium time:  %9.2f seconds\n",run_time/CLK_TCK);
  total_time = sort_time + run_time;
  fprintf(dev,"Total CPU time:              %9.2f seconds\n\n",
               total_time/CLK_TCK);
  fprintf(dev,"Largest deviation from zero:     %10.7f\n",market_clear());
  fclose(dev);
}
