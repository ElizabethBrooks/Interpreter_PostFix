% Name: Elizabeth Brooks
% Modified: 08 March 2017
% File: postfixInterpreter.pl

% Prolog Interpreter for PostFix:
% This interpreter takes the abstract syntax tree (AST), produced by the PostFix parser, and determines the result
% of a program for given input arguments.
% The AST is expressed as a Prolog list [Num, [Commands]], where Num represents the number of
% arguments to the program and [Commands] is a Prolog list of commands.

% The syntax of the PostFix language:
% program ::= (postfix number command_sequence)
% command_sequence ::= command command_sequence
% | L
% command ::= number
% | ( command_sequence )
% | 'add' | 'sub' | 'mul' | 'div' | 'rem'
% | 'lt' | 'eq' | 'gt'
% | 'pop'
% | 'swap'
% | 'sel'
% | 'nget'
% | 'exec'

% Gloassary:
% -add: Call the top stack value OpOne and the next-to-top stack value OpTwo. Pop these two values off the
% stack and push the result of OpTwo + OpOne onto the stack. 
% -sub: Call the top stack value OpOne and the next-to-top stack value OpTwo. Pop these two values off the
% stack and push the result of OpTwo − OpOne onto the stack.
% -mul: Call the top stack value OpOne and the next-to-top stack value OpTwo. Pop these two values off the
% stack and push the result of OpTwo * OpOne onto the stack.
% -div: Call the top stack value OpOne and the next-to-top stack value OpTwo. Pop these two values off the
% stack and push the result of OpTwo / OpOne onto the stack.
% -rem: Call the top stack value OpOne and the next-to-top stack value OpTwo. Pop these two values off the
% stack and push the result of mod(OpTwo,OpOne) onto the stack.
% -lt: Call the top stack value OpOne and the next-to-top stack value OpTwo. Pop these two values off the
% stack. If OpTwo < OpOne, then push a 1 (true) on the stack, otherwise push a 0 (false).
% -eq: Call the top stack value OpOne and the next-to-top stack value OpTwo. Pop these two values off the
% stack. If OpTwo = OpOne, then push a 1 (true) on the stack, otherwise push a 0 (false).
% -gt: Call the top stack value OpOne and the next-to-top stack value OpTwo. Pop these two values off the
% stack. If OpTwo > OpOne, then push a 1 (true) on the stack, otherwise push a 0 (false).
% -pop: Pop the top element off the stack and discard it. Signal an error if the stack is empty.
% -swap: Swap the top two elements of the stack. Signal an error if the stack has fewer than two values.
% -sel: Call the top three stack values OpOne, OpTwo, and OpThree. Pop these three values off the stack.
% If OpThree is the numeral 0, push OpOne onto the stack; if OpThree is a non-zero numeral, push OpTwo onto the stack.
% -nget: Call the top stack value OpIndex and the remaining stack values (from top down) OpOne, OpTwo, . . ., OpN.
% Pop OpIndex off the stack. If OpIndex is a numeral I, such that 1 ≤ I ≤ N, push OpI onto the stack.
% -exec: Pop the executable sequence from the top of the stack, and prepend its component commands
% onto the sequence of currently executing commands.

% Interpreter:
% This interpreter has the main Prolog rule: interpret(AST, Input)
% where AST is a Prolog list representation of the abstract syntax tree of the PostFix program, as described above,
% and Input is a Prolog list containing the integer arguments for the program.
% Using a Prolog list to represent the stack, the first command in the command sequence component is removed
% from the command sequence and evaluated on each evaluation step with cuts to prevent backtracking. 
% The result of the interpreter evaluations is an updated command sequence and stack.
 
% interpret rules:
interpret([],[Result|_],Output) :-
	number(Result),!,Output is Result.
interpret([NumOps,[]],CurrStack,CurrStack) :-
	number(NumOps),length(CurrStack,NumOps),!.
interpret([NumOps,[Token|RemainingList]],CurrStack,Output) :-
	number(NumOps),length(CurrStack,NumOps),!,
	evaluate(Token,CurrStack,NextStack),
	interpret(RemainingList,NextStack,Output).
interpret([Token|RemainingList],CurrStack,Output) :-
	evaluate(Token,CurrStack,NextStack),
	interpret(RemainingList,NextStack,Output).
% evaluate facts:
evaluate([ComH|ComT],CurrStack,[[ComH|ComT]|CurrStack]).
evaluate(swap,[OpOne,OpTwo|RemainingS],[OpTwo,OpOne|RemainingS]).
% evaluate rules:
evaluate(add,[OpOne,OpTwo|RemainingS],[Output|RemainingS]) :-
	number(OpOne),number(OpTwo),!,Output is OpTwo + OpOne.
evaluate(sub,[OpOne,OpTwo|RemainingS],[Output|RemainingS]) :-
	number(OpOne),number(OpTwo),!,Output is OpTwo - OpOne.
evaluate(mul,[OpOne,OpTwo|RemainingS],[Output|RemainingS]) :-
	number(OpOne),number(OpTwo),!,Output is OpTwo * OpOne.
evaluate(div,[OpOne,OpTwo|RemainingS],[Output|RemainingS]) :-
	number(OpOne),number(OpTwo),OpOne \= 0,!,Output is OpTwo / OpOne.
evaluate(rem,[OpOne,OpTwo|RemainingS],[Output|RemainingS]) :-
	number(OpOne),number(OpTwo),OpOne \= 0,!,Output is mod(OpTwo,OpOne).
evaluate(lt,[OpOne,OpTwo|RemainingS],[Output|RemainingS]) :-
	number(OpOne),number(OpTwo),OpTwo < OpOne,!,Output is 1.
evaluate(lt,[OpOne, OpTwo|RemainingS],[Output|RemainingS]) :-
	number(OpOne),number(OpTwo),OpOne < OpTwo,!,Output is 0.
evaluate(eq,[OpOne,OpTwo|RemainingS],[Output|RemainingS]) :-
	number(OpOne),number(OpTwo),OpTwo == OpOne,!,Output is 1.
evaluate(eq,[OpOne,OpTwo|RemainingS],[Output|RemainingS]) :-
	number(OpOne),number(OpTwo),OpTwo \= OpOne,!,Output is 0.
evaluate(gt,[OpOne,OpTwo|RemainingS],[Output|RemainingS]) :-
	number(OpOne),number(OpTwo),OpTwo > OpOne,!,Output is 0.
evaluate(gt,[OpOne,OpTwo|RemainingS],[Output|RemainingS]) :-
	number(OpOne),number(OpTwo),OpOne > OpTwo,!,Output is 1.
evaluate(pop,[OpOne|RemainingS],RemainingS) :-
	number(OpOne).
evaluate(sel,[OpOne,_,OpThree|RemainingS],[OpOne|RemainingS]) :-
	number(OpThree),OpThree == 0,!.
evaluate(sel,[_,OpTwo,OpThree|RemainingS],[OpTwo|RemainingS]) :- 
   	number(OpThree),OpThree \== 0,!.
evaluate(sel,[[OpOneH|OpOneT],_,OpThree|RemainingS],[[OpOneH|OpOneT]|RemainingS]) :-
	number(OpThree),OpThree == 0,!.
evaluate(sel,[_,[OpTwoH|OpTwoT],OpThree|RemainingS],[[OpTwoH|OpTwoT]|RemainingS]) :- 
   	number(OpThree),OpThree \== 0,!.
evaluate(nget,[OpOne|RemainingS],[Output|RemainingS]) :-
	number(OpOne),getN(OpOne,RemainingS,1,NGot),!,Output is NGot.
evaluate(exec,[[SeqH|SeqT]|RemainingS],NewS) :-
	execCom([SeqH|SeqT],RemainingS,NewS).
evaluate(NumOp,RemainingS,[NumOp|RemainingS]) :-
	number(NumOp).
% execCom fact:
execCom([],OutS,OutS).
% execCom rules:
execCom([ComOp|RemainingCom],ComS,OutS) :-
	evaluate(ComOp,ComS,NewS),
	execCom(RemainingCom,NewS,OutS).
% getN rules:
getN(OpOne,[NGot|_],Count,NGot) :-
    Count == OpOne,!.
getN(OpOne,[_|RemainingN],Count,NGot) :-
    Count < OpOne,Counter is Count + 1,getN(OpOne,RemainingN,Counter,NGot).