% Solution for the problem
% Modules necessary.
:- use_module(library(pairs)).
unload_last_source:-
  findall(Source, source_file(Source), LSource),
  reverse(LSource, [Source|_]),
  unload_source(Source).

unload_source(Source):-
  ground(Source),
  source_file(Pred, Source),
  functor(Pred, Functor, Arity),
  abolish(Functor/Arity),
  fail.
unload_source(_).

% Check Whether an execution schedule is valid.
isSolution(solution([Schedule|Schedules])):-
	isSchedule(Schedule, T1, C1),
	isSchedules(Schedules, T2, C2), 
	append(T1, T2, Tasks),
	append(C1, C2, Cores),
	findall(T, task(T), AllTasks),
	setof(X, member(X, Tasks), Taskset),
	length(AllTasks, Len),
	length(Taskset, Len),
	length(Tasks, Len),
	setof(X, member(X, Cores), Coreset),
	length(Coreset, Len2),
	length(Cores, Len2).
isSchedules([], [], []).
isSchedules([Schedule|Schedules], T, C):-
	isSchedule(Schedule, T1, C1),
	isSchedules(Schedules, T2, C2),
	append(T1, T2, T),
	append(C1, C2, C).
isSchedule(schedule(C, [T|Ts]), [T|Ts], [C]):- core(C), isTasks(T, Ts).
isTasks(T0, []):-task(T0).
isTasks(T0, [T|Ts]):-task(T0),isTasks(T, Ts).

% Calculate execution time for solution
execution_time(solution(Schedules), ET):-
	schedules_execution_time(Schedules, ETs),
	max_list(ETs, ET).
schedules_execution_time([],[]).
schedules_execution_time([Schedule|Schedules], ET):-
	schedules_execution_time(Schedules, ET2),
	schedule_execution_time(Schedule, ET1),
	append([ET1], ET2, ET).
schedule_execution_time(schedule(Core, Tasks), ET):-
	taskset_execution_time(Core, Tasks, ET).
taskset_execution_time(Core, [], 0):-core(Core).
taskset_execution_time(Core, [T|Ts], ET):-
	process_cost(T,Core,ET1),
	taskset_execution_time(Core, Ts, ET2),
	ET is ET1 + ET2.

% The function to find the best solution among a list of solutions.
find_best_schedule(Schedules, BestSchedule):-
	compare_schedules(Schedules, TempBestET, BestET, BestSchedule).
compare_schedules([], TempBestET, BestET, TempSol, BestSol):-
	BestET is TempBestET, 
	append(TempSol, [], BestSol).
compare_schedules([Solution|Solutions], BestET, TempSol, BestSol):-
	schedules_execution_time(Solution,ET1s),
	max_list(ET1s, ET1),
	append(Solution, [], TempSol),
	compare_schedules(Solutions, ET1, BestET, TempSol, BestSol).
compare_schedules([Solution|Solutions], TempBestET, BestET, TempSol, BestSol):-
	schedules_execution_time(Solution, ET1s),
	max_list(ET1s, ET1),
	(TempBestET > ET1,!, 
	compare_schedules(Solutions, ET1, BestET, Solution, BestSol);
	compare_schedules(Solutions, TempBestET, BestET, TempSol, BestSol)).

% Finds an execution schedule S, exactly minimizing execution time.
find_optimal(optimal_solution(BestSol, ET)):-
	findall(Task, task(Task), AllTasks),
	findall(Core, core(Core), AllCores),
	generate_all_solutions(50, AllTasks, AllCores,SolutionList),
	%generate_potential_solutions(1500,SolutionList),
	compare_solution(SolutionList, ET, [BestSol]).
compare_solution([Solution], BestET, BestSol):-
	execution_time(Solution, BestET),
	append([Solution], [] ,BestSol).
compare_solution([Solution|Solutions], BestET, BestSol):-
	compare_solution(Solutions, TempBestET, TempSol),
	execution_time(Solution, CurrentET),
	(TempBestET > CurrentET,!, 
	BestET is CurrentET,
	append([Solution], [], BestSol);
	BestET is TempBestET,
	append(TempSol, [], BestSol)).

%Generate solution For Homo Sets.
generate_potential_solutions(0 ,Solution):-
	append([],[],Solution).
generate_potential_solutions(Limit, Solution):-
	NewLimit is Limit - 1, 
	findall(Task, task(Task), AllTasks),
	findall(Core, core(Core), AllCores),
	sort_all_tasks(AllTasks, SortedTasks),
	my_reverse(SortedTasks, RevSortedTasks),
	generate_potential_solution(Sol, AllCores, RevSortedTasks),
	generate_potential_solutions(NewLimit, Solutions),
	append([solution(Sol)], Solutions, Solution).
	% Sort all tasks by execution time.
	sort_all_tasks(AllTasks, SortedTasks):-
		get_et_list(AllTasks, AllETs),
		map_lists_to_pairs(AllTasks, AllETs, Pairs),
	    keysort(Pairs, Sorted),
		pairs_values(Sorted, SortedTasks).
		
		get_et_list([], AllETs):-
			append([],[],AllETs).
		get_et_list([Task|Tasks], AllETs):-
			process_cost(Task, c1, ET),
			get_et_list(Tasks, AllET),
			append([ET], AllET, AllETs).
	map_lists_to_pairs([], [], Pairs):-
		append([], [], Pairs).
	map_lists_to_pairs([Task|Tasks], [ET|ETs], Pairs):-
		map_lists_to_pairs(Tasks, ETs, Pairs1),
		append([(ET-Task)], Pairs1, Pairs).
	my_reverse(L1,L2) :- my_rev(L1,L2,[]).
	my_rev([],L2,L2) :- !.
	my_rev([X|Xs],L2,Acc) :- my_rev(Xs,L2,[X|Acc]).
	%Generate solution now.
	generate_potential_solution(Solution, Cores, Tasks):-
		length(Cores, CoreLength),
		split_tasksets(Tasks, CoreLength, SplittedTasksets),
		organize_tasksets(SplittedTasksets, CoreLength, OrganizedTasksets),
		generate_potential_schedule(Cores, OrganizedTasksets, Solution).
		%Split tasks into small sets with length of cores.
		split_tasksets(Tasks, CoreLength, SplittedTasks):-
			length(Tasks, TaskLength),
			TaskLength =< CoreLength, ! ,
			rnd_permu(Tasks, PermutedTasks),
			append([PermutedTasks], [], SplittedTasks);
			split(Tasks, CoreLength, Taskset, TaskRemained),
			rnd_permu(Taskset, PermutedTaskset),
			split_tasksets(TaskRemained, CoreLength, OrganizedTasks2),
			append([PermutedTaskset], OrganizedTasks2, SplittedTasks).
		organize_tasksets(SplittedTasks, CoreLength, OrganizedTasks):- 
			Counter is 1,
			organize_taskset(SplittedTasks, Counter, OrganizedTaskset),
			organize_tasksets(SplittedTasks, CoreLength, OrganizedTasksets, Counter),
			append(OrganizedTasksets, [OrganizedTaskset], OrganizedTasks).
		organize_tasksets(SplittedTasks, CoreLength, OrganizedTasks, CoreLength):-
			append([], [], OrganizedTasks).
		organize_tasksets(SplittedTasks, CoreLength, OrganizedTasks, Counter):-
			NewCounter is Counter + 1,
			organize_taskset(SplittedTasks, NewCounter, OrganizedTaskset),
			organize_tasksets(SplittedTasks, CoreLength, OrganizedTasksets, NewCounter),
			append(OrganizedTasksets, [OrganizedTaskset], OrganizedTasks).
		organize_taskset([], Counter, OrganizedTasks):-
			append([],[],OrganizedTasks).
		organize_taskset([SplittedTask|SplittedTasks], Counter, OrganizedTasks):-
			length(SplittedTask, TaskLength),
			TaskLength < Counter, !,
			append([],[],OrganizedTasks);
			nth1(Counter, SplittedTask, Element),
			organize_taskset(SplittedTasks, Counter, OrganizedTasks2),
			append([Element], OrganizedTasks2, OrganizedTasks).
		generate_potential_schedule([], [], Solution):-
			append([], [], Solution).
		generate_potential_schedule([Core|Cores], [OrganizedTaskset|OrganizedTasksets], Solution):-
			generate_potential_schedule(Cores, OrganizedTasksets, Schedules),
			append([schedule(Core, OrganizedTaskset)], Schedules, Solution).

% Generate Solution For Hetero Set.
generate_all_solutions(0, AllTasks, AllCores, TempList, List):- 
	append(TempList, [], List).
generate_all_solutions(Limit, AllTasks, AllCores, List):-
	rnd_permu(AllTasks, PermutedTasks),
	generate_solution(AllCores, PermutedTasks, Solution),!,
	NewLimit is Limit -1,
	append([solution(Solution)],[], TempList),
	generate_all_solutions(NewLimit, AllTasks, AllCores, TempList, List).
generate_all_solutions(Limit, AllTasks, AllCores, TempList, List):-
	rnd_permu(AllTasks, PermutedTasks),
	generate_solution(AllCores, PermutedTasks, Solution),!,
	NewLimit is Limit -1,
	append([solution(Solution)],TempList, NewTempList),
	generate_all_solutions(NewLimit, AllTasks, AllCores, NewTempList, List).
	
	generate_solution(AllCores, [], Schedules):-
		generate_basic_solution(AllCores, Schedules).
	generate_solution(AllCores, [Task|Tasks], Schedules):-
		generate_solution(AllCores, Tasks, TempSchedules),
		get_the_optimal_subschedules(AllCores, Task, TempSchedules, AllSchedules),
		find_best_schedule(AllSchedules, Schedules).

	generate_basic_solution([], Schedules):-
		append([],[],Schedules).
	generate_basic_solution([Core|Cores], Schedules):-
		generate_basic_solution(Cores, TempSchedules),
		append([schedule(Core, [])], TempSchedules, Schedules).

	get_the_optimal_subschedules([Core], Task, Schedules, AllSchedules):-
		generate_subschedules(Core, Task, Schedules, NewSchedules),
		append([NewSchedules], [], AllSchedules).
	get_the_optimal_subschedules([Core|Cores], Task, Schedules, AllSchedules):-
		get_the_optimal_subschedules(Cores, Task, Schedules, TempBestSchedules),
		generate_subschedules(Core, Task, Schedules, NewSchedules),
		append([NewSchedules], TempBestSchedules, AllSchedules).

	generate_subschedules(Core, Task, [], NewSchedules):-
		append([], [], NewSchedules).
	generate_subschedules(Core, Task, [schedule(Core,Tasks)|Schedules], NewSchedules):-
		generate_subschedules(Core, Task, Schedules, TempSchedules),
		append([Task], Tasks, NewTasks),
		append([schedule(Core, NewTasks)], TempSchedules, NewSchedules).
	generate_subschedules(Core, Task, [Schedule|Schedules], NewSchedules):-
		generate_subschedules(Core, Task, Schedules, TempSchedules),
		append([Schedule], TempSchedules, NewSchedules).

%Solution for denpendency.
generate_dependency_solution(solution(Solution)):-
	findall(Task, task(Task), AllTasks),
	findall(Core, core(Core), AllCores),
	sort_tasks([t1], SortedTasks),
	append([t1], SortedTasks, SortedTasks2),
	findall_critical_path(SortedTasks2, Paths),
	form_schedules(AllCores, Paths, Solution).

	sort_tasks([], SortedTasks):-
		append([], [], SortedTasks).
	sort_tasks([Task|Tasks], SortedTasks):-
		findall(SubTask, depends_on(SubTask, Task, _), SubTasks),
		sort_tasks(Tasks, TempSortedTasks),
		sort_tasks(SubTasks, SortedSubtasks),
		append(SubTasks, TempSortedTasks, CurrentLevelTask),
		append(CurrentLevelTask, SortedSubtasks, SortedTasks).

	form_schedules(AllCores, [], Solution):-
		generate_basic_solution(AllCores, Schedules).
	form_schedules(AllCores, [Path|Paths], Solution):-
		form_schedules(Cores, Paths, SubSolution),
		assign_path(Path, SubSolution, Solution).

		assign_path(Path, SubSolution, Solution).


	findall_critical_path(AllTasks, Paths):-
		(length(AllTasks, 0), !,
		append(AllTasks, [], Paths);
		nth1(1, AllTasks, Task),
		find_critical_path(Task, AllTasks, CriticalPath),
		remove_items(CriticalPath, AllTasks, RemainedTasks),
		findall_critical_path(RemainedTasks, GainedPaths),
		append([CriticalPath], GainedPaths, Paths)).
	find_critical_path([], CriticalPath, CriticalPaths):-
		append([], [], CriticalPaths).
	find_critical_path([Task|Tasks], CriticalPath, CriticalPaths):-
		findall(SubTask, depends_on(SubTask, Task, _), SubTasks),
		(length(SubTasks, 0), !,
		append(CriticalPath, [Task], OneCriticalPath),
		append([OneCriticalPath], [], CriticalPaths);
		append(CriticalPath, [Task], NewCriticalPath),
		find_critical_path(Tasks, CriticalPath, OtherPaths),
		find_critical_path(SubTasks, NewCriticalPath, Paths),
		append(Paths, OtherPaths, CriticalPaths)).


	remove_items([], AllTasks, RemainedTasks):-
		append(AllTasks, [], RemainedTasks).
	remove_items([Item|Items], AllTasks, RemainedTasks):-
		remove_items(Items, AllTasks, TempRemainedTasks),
		delete(TempRemainedTasks, Item, RemainedTasks).

% Randomly select item from the list.
rnd_select(_,0,[]).
rnd_select(Xs,N,[X|Zs]) :- N > 0,
    length(Xs,L),
    I is random(L) + 1,
    remove_at(X,Xs,I,Ys),
    N1 is N - 1,
    rnd_select(Ys,N1,Zs).

% Generate the permutation of a list.
rnd_permu(L1,L2) :- length(L1,N), rnd_select(L1,N,L2).
remove_at(X,[X|Xs],1,Xs).
remove_at(X,[Y|Xs],K,[Y|Ys]) :- K > 1, 
   K1 is K - 1, remove_at(X,Xs,K1,Ys).  

% Split a list into two parts.
split(L,0,[],L).
split([X|Xs],N,[X|Ys],Zs) :- N > 0, N1 is N - 1, split(Xs,N1,Ys,Zs).

% length frequency sort
lfsort(InList,OutList) :- lfsort(InList,OutList,asc).

% sorting direction Dir is either asc or desc
lfsort(InList,OutList,Dir) :-
	add_key(InList,KList,desc),
   keysort(KList,SKList),
   pack(SKList,PKList),
   lsort(PKList,SPKList,Dir),
   flatten(SPKList,FKList),
   rem_key(FKList,OutList).
   
pack([],[]).
pack([L-X|Xs],[[L-X|Z]|Zs]) :- transf(L-X,Xs,Ys,Z), pack(Ys,Zs).

%find_best_schedule([[schedule(c1, [t3]), schedule(c2, []), schedule(c3, [])], [schedule(c1, []), schedule(c2, [t3]), schedule(c3, [])], [schedule(c1, []), schedule(c2, []), schedule(c3, [t3])]], [[schedule(c1, [t3]), schedule(c2, []), schedule(c3, [])]])creep
%find_best_schedule([[schedule(c1, [t2, t3]), schedule(c2, []), schedule(c3, [])], [schedule(c1, [t3]), schedule(c2, [t2]), schedule(c3, [])], [schedule(c1, [t3]), schedule(c2, []), schedule(c3, [t2])]], [schedule(c1, [t3]), schedule(c2, [t2]), schedule(c3, [])])
%find_best_schedule([[schedule(c1, [t3]), schedule(c2, []), schedule(c3, [])], [schedule(c1, []), schedule(c2, [t3]), schedule(c3, [])], [schedule(c1, []), schedule(c2, []), schedule(c3, [t3])]], [schedule(c1, [t3]), schedule(c2, []), schedule(c3, [])])creep

