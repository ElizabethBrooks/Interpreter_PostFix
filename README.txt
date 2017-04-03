% Name: Elizabeth Brooks
% Modified: 08 March 2017
% File: README.txt

% CSCI 512, Assignment 1: GNU Prolog Implementations

% First, load the Prolog files for Assignment 1 using the following commands:
?- ['/.../CSCI512_V2_Assignment1_Brookse/scanner'].
?- ['/.../CSCI512_V2_Assignment1_Brookse/postfixParser'].
?- ['/.../CSCI512_V2_Assignment1_Brookse/postfixInterpreter'].

% Second, run the scanner on input text file T representing a PostFix program:
?- scan('/.../filename.txt',T).

% Third, run the parser on the prolog list of commands T after scanning:
?- parse(T,A).

% Finally, run the interpreter on the Abstract Syntax Tree A and input stack S after scanning and parsing:
?- interpret(A,S,P).

% Alternatively, the Abstract SYntax Tree may be manually entered as the first argument to the interpreter, for example:
?- interpret([3,[1,nget,1,swap,lt,[10,lt,[0],[mul],sel,exec],[pop,mul],sel,exec]],[3,6,8],P).

% Potential bugs:
% postfixParser appears to continuously recurse on the first exprCom fact, exprCom([[number,Val]|RestIn],RestIn,[Val]) during parsing.
% postfixParser2 similarly loops on the first parseAST fact, parseAST([[number,Val]|RestIn],RestIn,BuildAST,[Val|BuildAST]) during parsing.

% Sample program evocation and results:
| ?- ['/Users/Camel/Desktop/scanner'].
yes

| ?- ['/Users/Camel/Desktop/postfixParser'].
yes

| ?- ['/Users/Camel/Desktop/postfixInterpreter'].
yes

| ?- scan('/Users/Camel/Desktop/testPostfix.txt',T).
T = [[punctuation,'('],[identifier,postfix],[number,1],[number,4],[identifier,add],[number,5],[identifier,mul],[number,6],[identifier,sub],[number,7],[identifier,div],[punctuation,')'],[punctuation,eof]]
yes

| ?- parse(T,A).
A = [B,[]]
T = [[punctuation,'('],[identifier,postfix],[number,B],[punctuation,')'],[punctuation,eof]] ?
yes

| ?- interpret(A,[3],P).
A = []
P = 3
yes

| ?- interpret([1,[4,add,5,mul,6,sub,7,div]],[3],P).
P = 4.1428571428571432
yes

| ?- scan('/Users/Camel/Desktop/testPostfix2.txt',T2).
T2 = [[punctuation,'('],[identifier,postfix],[number,3],[number,1],[identifier,nget],[number,1],[identifier,swap],[identifier,lt],[punctuation,'('],[number,10],[identifier,lt],[punctuation,'('],[number,0],[punctuation,')'],[punctuation,'('],[identifier,mul],[punctuation,')'],[identifier,sel],[identifier,exec],[punctuation,')'],[punctuation,'('],[identifier,pop],[identifier,mul],[punctuation,')'],[identifier,sel],[identifier,exec],[punctuation,')'],[punctuation,eof]]
yes

| ?- parse(T2,A2).
A2 = [A,[]]
T2 = [[punctuation,'('],[identifier,postfix],[number,A],[punctuation,')'],[punctuation,eof]] ?
yes

| ?- interpret(A2,[3,6,8],P2).
A2 = []
P2 = 3
yes

| ?- interpret([3,[1,nget,1,swap,lt,[10,lt,[0],[mul],sel,exec],[pop,mul],sel,exec]],[3,6,8],P2).
P2 = 0
yes

% Sample program evocation and results: alternate PostFix parser (postfixParser2)
| ?- ['/Users/Camel/Desktop/postfixParser2'].
yes

| ?- scan('/Users/Camel/Desktop/testPostfix.txt',T).
T = [[punctuation,'('],[identifier,postfix],[number,1],[number,4],[identifier,add],[number,5],[identifier,mul],[number,6],[identifier,sub],[number,7],[identifier,div],[punctuation,')'],[punctuation,eof]]
yes

| ?- parse(T,A).
A = []
T = [] ?
yes

| ?- interpret(A,[3],P).
A = []
P = 3
yes