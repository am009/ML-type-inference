\title{
$1 M L$
}

\section*{By François Pottier and Didier Rémy}

\subsection*{1.1 Preliminaries}

\section*{Names and renaming}

Mathematicians and computer scientists use names to refer to arbitrary or unknown objects in the statement of a theorem, to refer to the parameters of a function, etc. Names are convenient because they are understandable by humans; nevertheless, they can be tricky. An in-depth treatment of the difficulties associated with names and renaming is beyond the scope of the present chapter: we encourage the reader to study Gabbay and Pitts' excellent series of papers (Gabbay and Pitts, 2002; Pitts, 2002b). Here, we merely recall a few notions that are used throughout this chapter. Consider, for instance, an inductive definition of the abstract syntax of a simple programming language, the pure $\lambda$-calculus:

$$
\mathrm{t}::=\mathrm{z}|\lambda \mathrm{z} . \mathrm{t}| \mathrm{t} \mathrm{t}
$$

Here, the meta-variable $\mathrm{z}$ ranges over an infinite set of variables - that is, names-while the meta-variable t ranges over terms. As usual in mathematics, we write "the variable $z$ " and "the term $t$ " instead of "the variable denoted by $z$ " and "the term denoted by t". The above definition states that a term may be a variable $\mathbf{z}$, a pair of a variable and a term, written $\lambda$ z.t, or a pair of terms, written $t_{1} t_{2}$. However, this is not quite what we need. Indeed, according to
\footnotetext{
The (currently unfinished) code that accompanies this chapter may be found at http: //pauillac.inria.fr/ remy/mlrow/. For space reasons, some material, including proofs, exercises, and more, has been left out of this version. In the future, a full version of this chapter that includes the missing material will be made available at the same address. In spite of these omissions, this chapter is still oversize with respect to Benjamin's 100 page barrier: we currently have roughly 135 pages of text and 15 pages of solutions to exercises. We would appreciate comments and suggestions from the proofreaders as to how this chapter could be made shorter, without severely compromising its interest or readability.
}
this definition, the terms $\lambda z_{1} \cdot z_{1}$ and $\lambda z_{2} \cdot z_{2}$ are distinct, while we would like them to be a single mathematical object, because we intend $\lambda z . z$ to mean "the function that maps $z$ to $z$ "- a meaning that is independent of the name $z$. To achieve this effect, we complete the above definition by stating that the construction $\lambda$ z.t binds $\mathbf{z}$ within $t$. One may also say that $\lambda \mathrm{z}$ is a binder whose scope is $t$. Then, $\lambda z . t$ is no longer a pair: rather, it is an abstraction of the variable $z$ within the term $t$. Abstractions have the property that the identity of the bound variable does not matter; that is, $\lambda z_{1} . z_{1}$ and $\lambda z_{2} . z_{2}$ are the same term. Informally, we say that terms are considered equal modulo $\alpha$-conversion. Once the position and scope of binders are known, several standard notions follow, such as the set of free variables of a term $t$, written $f v(t)$, and the capture-avoiding substitution of a term $t_{1}$ for a variable $z$ within a term $t_{2}$, written $\left[\mathrm{z} \mapsto \mathrm{t}_{1}\right] \mathrm{t}_{2}$. For conciseness, we write $f v\left(\mathrm{t}_{1}, \mathrm{t}_{2}\right)$ for $f v\left(\mathrm{t}_{1}\right) \cup f v\left(\mathrm{t}_{2}\right)$. A term is said to be closed when it has no free variables.

A renaming is a total bijective mapping from variables to variables that affects only a finite number of variables. The sole property of a variable is its identity, that is, the fact that it is distinct from other variables. As a result, at a global level, all variables are interchangeable: if a theorem holds in the absence of hypotheses about any particular variable, then any renaming of it holds as well. We often make use of this fact. When proving a theorem $T$, we say that a hypothesis $H$ may be assumed wihout loss of generality (w.l.o.g.) if the theorem $T$ follows from the theorem $H \Rightarrow T$ via a renaming argument, which is usually left implicit.

If $\bar{z}_{1}$ and $\bar{z}_{2}$ are sets of variables, we write $\bar{z}_{1} \# \bar{z}_{2}$ as a shorthand for $\overline{\mathrm{z}}_{1} \cap \overline{\mathrm{z}}_{2}=\varnothing$, and say that $\overline{\mathrm{z}}_{1}$ is fresh for $\overline{\mathrm{z}}_{2}$ (or vice-versa). We say that $\overline{\mathrm{z}}$ is fresh for $t$ if and only if $\bar{z} \# \mathrm{fv}(\mathrm{t})$ holds.

In this chapter, we work with several distinct varieties of names: program variables, memory locations, and type variables, the latter of which may be further divided into kinds. We draw names of different varieties from disjoint sets, each of which is infinite.

\subsection*{1.2 What is ML?}

The name "ML" appeared during the late seventies. It then referred to a general-purpose programming language that was used as a meta-language (whence its name) within the theorem prover LCF (Gordon, Milner, and Wadsworth, 1979b). Since then, several new programming languages, each of which offers several different implementations, have drawn inspiration from it. So, what does "ML" stand for today?

For a semanticist, "ML" might stand for a programming language featuring first-class functions, data structures built out of products and sums, mutable
memory cells called references, exception handling, automatic memory management, and a call-by-value semantics. This view encompasses the Standard ML (Milner, Tofte, and Harper, 1990) and Caml (Leroy, 2000) families of programming languages. We refer to it as $M L$-the-programming-language.

For a type theorist, "ML" might stand for a particular breed of type systems, based on the simply-typed $\lambda$-calculus, but extended with a simple form of polymorphism introduced by let declarations. These type systems have decidable type inference; their type inference algorithms crucially rely on first-order unification and can be made efficient in practice. In addition to Standard ML and Caml, this view encompasses programming languages such as Haskell (Hudak, Peyton Jones, Wadler, Boutel, Fairbairn, Fasel, Guzman, Hammond, Hughes, Johnsson, Kieburtz, Nikhil, Partain, and Peterson, 1992) and Clean (Brus, van Eekelen, van Leer, and Plasmeijer, 1987), whose semantics is rather different-indeed, it is pure and lazy-but whose type system fits this description. We refer to it as $M L$-the-type-system. It is also referred to as Hindley and Milner's type discipline in the literature.

For us, "ML" might also stand for the particular programming language whose formal definition is given and studied in this chapter. It is a core calculus featuring first-class functions, let declarations, and constants. It is equipped with a call-by-value semantics. By customizing constants and their semantics, one may recover data structures, references, and more. We refer to this particular calculus as $M L$-the-calculus.

Why study ML-the-type-system today, such a long time after its initial discovery? One may think of at least two reasons.

First, its treatment in the literature is often cursory, because it is considered either as a simple extension of the simply-typed $\lambda$-calculus (TAPL Chapter 9) or as a subset of Girard and Reynolds' System F (TAPL Chapter 23). The former view is supported by the claim that the let construct, which distinguishes ML-the-type-system from the simply-typed $\lambda$-calculus, may be understood as a simple textual expansion facility. However, this view only tells part of the story, because it fails to give an account of the principal types property enjoyed by ML-the-type-system, leads to a naïve type inference algorithm whose time complexity is exponential, and breaks down when the language is extended with side effects, such as state or exceptions. The latter view is supported by the fact that every type derivation within ML-the-type-system is also a valid type derivation within an implicity-typed variant of System F. Such a view is correct, but again fails to give an account of type inference for ML-the-type-system, since type inference for System F is undecidable (Wells, 1999).

Second, existing accounts of type inference for ML-the-type-system (Milner, 1978; Damas and Milner, 1982; Tofte, 1988; Leroy, 1992; Lee and Yi, 1998;

Jones, 1999) usually involve heavy manipulations of type substitutions. Such an ubiquitous use of type substitutions is often quite obscure. Furthermore, actual implementations of the type inference algorithm do not explicitly manipulate substitutions; instead, they extend a standard first-order unification algorithm, where terms are updated in place as new equations are discovered (Huet, 1976). Thus, it is hard to tell, from these accounts, how to write an efficient type inference algorithm for ML-the-type-system. Yet, in spite of the increasing speed of computers, efficiency remains crucial when ML-thetype-system is extended with expensive features, such as Objective Caml's object types (Rémy and Vouillon, 1998) or polymorphic methods (Garrigue and Rémy, 1999).

For these reasons, we believe it is worth giving an account of ML-the-typesystem that focuses on type inference and strives to be at once elegant and faithful to an efficient implementation. To achieve these goals, we forego type substitutions and instead put emphasis on constraints, which offer a number of advantanges. First, constraints allow a modular presentation of type inference as the combination of a constraint generator and a constraint solver. Such a decomposition allows reasoning separately about when a program is correct, on the one hand, and how to check whether it is correct, on the other hand. It has long been standard in the setting of the simply-typed $\lambda$ calculus (TAPL Chapter 22), but, to the best of our knowledge, has never been proposed for ML-the-type-system. Second, it is often natural to define and implement the solver as a constraint rewriting system. Then, the constraint language allows reasoning not only about correctness-is every rewriting step meaning-preserving?-but also about low-level implementation details, since constraints are the data structures manipulated throughout the type inference process. For instance, describing unification in terms of multiequations (Jouannaud and Kirchner, 1991) allows reasoning about the sharing of nodes in memory, which a substitution-based approach cannot account for. Last, constraints are more general than type substitutions, and allow describing many extensions of ML-the-type-system, among which extensions with recursive types, rows, subtyping, first-order unification under a mixed prefix, and more.

Before delving into the details of this new presentation of ML-the-typesystem, however, it is worth recalling its standard definition. Thus, in what follows, we first define the syntax and operational semantics of the programming language ML-the-calculus, and equip it with a type system, known as Damas and Milner's type system.

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-005.jpg?height=564&width=1520&top_left_y=223&top_left_x=222)

Figure 1-1: Syntax of ML-the-calculus

\section*{ML-the-calculus}

The syntax of ML-the-calculus is defined in Figure 1-1. It is made up of several syntactic categories.

Identifiers group several kinds of names that may be referenced in a program: variables, memory locations, and constants. We let $\mathrm{x}$ and $\mathrm{y}$ range over identifiers. Variables-sometimes called program variables to avoid ambiguity — are names that may be bound to values using $\lambda$ or let binding forms; in other words, they are names for function parameters or local definitions. We let $z$ and $f$ range over program variables. We sometimes write _ for a program variable that does not occur free within its scope: for instance, $\lambda_{\text {_.t stands for }} \lambda$ z.t, provided $\mathrm{z}$ is fresh for $t$. Memory locations are names that represent memory addresses. By convention, memory locations never appear in source programs, that is, programs that are submitted to a compiler. They only appear during execution, when new memory blocks are allocated. Constants are fixed names for primitive values and operations, such as integer literals and integer arithmetic operations. Constants are elements of a finite or infinite set $\mathcal{Q}$. They are never subject to $\alpha$-conversion. Program variables, memory locations, and constants belong to distinct syntactic classes and may never be confused.

The set of constants $\mathcal{Q}$ is kept abstract, so most of our development is independent of its concrete definition. We assume that every constant $\mathrm{c}$ has a nonnegative integer arity $a(\mathrm{c})$. We further assume that $\mathcal{Q}$ is partitioned into subsets of constructors $\mathcal{Q}^{+}$and destructors $\mathcal{Q}^{-}$. Constructors and destructors differ in that the former are used to form values, while the latter are used to
operate on values.

1.2.1 ExAmple [IntEgERs]: For every integer $n$, one may introduce a nullary constructor $\hat{n}$. In addition, one may introduce a binary destructor $\hat{+}$, whose applications are written infix, so $t_{1} \hat{+} t_{2}$ stands for the double application $\hat{+} t_{1} t_{2}$ of the destructor $\hat{+}$ to the expressions $t_{1}$ and $t_{2}$.

Expressions - also known as program terms or programs - are the main syntactic category. Indeed, unlike procedural languages such as $\mathrm{C}$ and Java, functional languages, including ML-the-programming-language, suppress the distinction between expressions and statements. Expressions include identifiers, $\lambda$-abstractions, applications, and local definitions. The $\lambda$-abstraction $\lambda$ z.t represents the function of one parameter named $z$ whose result is the expression $t$, or, in other words, the function that maps $z$ to $t$. Note that the variable $z$ is bound within the term $t$, so (for instance) $\lambda z_{1} \cdot z_{1}$ and $\lambda z_{2} \cdot z_{2}$ are the same object. The application $t_{1} t_{2}$ represents the result of calling the function $t_{1}$ with actual parameter $t_{2}$, or, in other words, the result of applying $t_{1}$ to $t_{2}$. Application is left-associative, that is, $t_{1} t_{2} t_{3}$ stands for $\left(t_{1} t_{2}\right) t_{3}$. The construct let $z=t_{1}$ in $t_{2}$ represents the result of evaluating $t_{2}$ after binding the variable $z$ to $t_{1}$. Note that the variable $z$ is bound within $t_{2}$, but not within $t_{1}$, so for instance let $z_{1}=z_{1}$ in $z_{1}$ and let $z_{2}=z_{1}$ in $z_{2}$ are the same object. The construct let $z=t_{1}$ in $t_{2}$ has the same meaning as $\left(\lambda z . t_{2}\right) t_{1}$, but is dealt with in a more flexible way by ML-the-type-system. To sum up, the syntax of ML-the-calculus is that of the pure $\lambda$-calculus, extended with memory locations, constants, and the let construct.

Values form a subset of expressions. They are expressions whose evaluation is completed. Values include identifiers, $\lambda$-abstractions, and applications of constants, of the form $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k}$, where $k$ does not exceed $\mathrm{c}$ 's arity if $\mathrm{c}$ is a constructor, and $k$ is smaller than c's arity if $\mathrm{c}$ is a destructor. In what follows, we are often interested in closed values, that is, values that do not contain any free program variables. We use the meta-variables $v$ and $w$ for values.

1.2.2 Example: The integer literals $\ldots, \widehat{-1}, \hat{0}, \hat{1}, \ldots$ are nullary constructors, so they are values. Integer addition $\hat{+}$ is a binary destructor, so it is a value, and so is every partial application $\hat{+} \mathrm{v}$. Thus, both $\hat{+} \hat{1}$ and $\hat{+} \hat{+}$ are values. An application of $\hat{+}$ to two values, such as $\hat{2} \hat{+} \hat{2}$, is not a value.

1.2.3 EXAmple [Pairs]: Let $(\cdot, \cdot)$ be a binary constructor. If $t_{1}$ are $t_{2}$ are expressions, then the double application $(\cdot, \cdot) t_{1} t_{2}$ may be called the pair of $t_{1}$ and $t_{2}$, and may be written $\left(t_{1}, t_{2}\right)$. By the definition above, $\left(t_{1}, t_{2}\right)$ is a value if and only if $t_{1}$ and $t_{2}$ are both values.

Stores are finite mappings from memory locations to closed values. A store $\mu$ represents what is usually called a heap, that is, a collection of data structures,
each of which is allocated at a particular address in memory and may contain pointers to other elements of the heap. ML-the-programming-language allows overwriting the contents of an existing memory block-an operation sometimes referred to as a side effect. In the operational semantics, this effect is achieved by mapping an existing memory location to a new value. We write $\varnothing$ for the empty store. We write $\mu[m \mapsto \mathrm{v}]$ for the store that maps $m$ to $\mathrm{v}$ and otherwise coincides with $\mu$. When $\mu$ and $\mu^{\prime}$ have disjoint domains, we write $\mu \mu^{\prime}$ for their union. We write $\operatorname{dom}(\mu)$ for the domain of $\mu$ and range $(\mu)$ for the set of memory locations that appear in its codomain.

The operational semantics of a purely functional language, such as the pure $\lambda$-calculus, may be defined as a rewriting system on expressions. Because MLthe-calculus has side effects, however, we define its operational semantics as a rewriting system on configurations. A configuration $t / \mu$ is a pair of an expression $t$ and a store $\mu$. The memory locations in the domain of $\mu$ are considered bound within $t / \mu$, so (for instance) $m_{1} /\left(m_{1} \mapsto \hat{0}\right)$ and $m_{2} /\left(m_{2} \mapsto \hat{0}\right)$ are the same object. In what follows, we are often interested in closed configurations, that is, configurations $t / \mu$ such that $t$ has no free program variables and every memory location that appears within $t$ or within the range of $\mu$ is in the domain of $\mu$. If $t$ is a source program, its evaluation begins within an empty store-that is, with the configuration $t / \varnothing$. Because, by convention, source programs do not contain memory locations, this is a closed configuration. Furthermore, we shall see that all reducts of a closed configuration are closed as well. Please note that, instead of separating expressions and stores, it is possible to make store fragments part of the syntax of expressions; this idea, proposed in (Crank and Felleisen, 1991), is reminiscent of the encoding of reference cells in process calculi (Turner, 1995; Fournet and Gonthier, 1996).

A context is an expression where a single subexpression has been replaced with a hole, written [. Evaluation contexts form a strict subset of contexts. In an evaluation context, the hole is meant to highlight a point in the program where it is valid to apply a reduction rule. Thus, the definition of evaluation contexts determines a reduction strategy: it tells where and in what order reduction steps may occur. For instance, the fact that $\lambda z$. $]$ is not an evaluation context means that the body of a function is never evaluated-that is, not until the function is applied, see R-BETA below. The fact that $t \mathcal{E}$ is an evaluation context only if $t$ is a value means that, to evaluate an application $t_{1} t_{2}$, one should fully evaluate $t_{1}$ before attempting to evaluate $t_{2}$. More generally, in the case of a multiple application, it means that arguments should be evaluated from left to right. Of course, other choices could be made: for instance, defining $\mathcal{E}::=\ldots|\mathrm{t} \mathcal{E}| \mathcal{E} \mathrm{v} \mid \ldots$ would enforce a right-to-left evaluation order, while defining $\mathcal{E}::=\ldots \mid$ t $\mathcal{E}|\mathcal{E} \mathrm{t}| \ldots$ would leave the evaluation order unspecified, effectively allowing reduction to alternate between

\begin{tabular}{|c|c|c|c|}
\hline let $z=v$ in $t \longrightarrow[z \mapsto v] t$ & \begin{tabular}{l} 
(R-BETA) \\
(R-LET)
\end{tabular} & \begin{tabular}{c}
$\mathrm{t} / \mu \longrightarrow \mathrm{t}^{\prime} / \mu^{\prime}$ \\
$\operatorname{dom}\left(\mu^{\prime \prime}\right) \# \operatorname{dom}\left(\mu^{\prime}\right)$ \\
$\frac{\operatorname{range}\left(\mu^{\prime \prime}\right) \# \operatorname{dom}\left(\mu^{\prime} \backslash \mu\right)}{\mathrm{t} / \mu \mu^{\prime \prime} \longrightarrow \mathrm{t}^{\prime} / \mu^{\prime} \mu^{\prime \prime}}$
\end{tabular} & (R-ExtEnd) \\
\hline$\frac{\mathrm{t} / \mu \xrightarrow{\delta} \mathrm{t}^{\prime} / \mu^{\prime}}{\mathrm{t} / \mu \longrightarrow \mathrm{t}^{\prime} / \mu^{\prime}}$ & (R-Delta) & $\frac{\mathrm{t} / \mu \longrightarrow \mathrm{t}^{\prime} / \mu^{\prime}}{\mathcal{E}[\mathrm{t}] / \mu \longrightarrow \mathcal{E}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}}$ & (R-CONTEXT) \\
\hline
\end{tabular}

Figure 1-2: Semantics of ML-the-calculus

both subexpressions, and making evaluation nondeterministic. The fact that let $\mathrm{z}=\mathrm{v}$ in $\mathcal{E}$ is not an evaluation context means that the body of a local definition is never evaluated - that is, not until the definition itself is reduced, see R-LET below. We write $\mathcal{E}[\mathrm{t}]$ for the expression obtained by replacing the hole in $\mathcal{E}$ with the expression $t$.

Figure 1-2 defines first a relation $\longrightarrow$ between configurations, then a relation $\longrightarrow$ between closed configurations. If $\mathrm{t} / \mu \longrightarrow \mathrm{t}^{\prime} / \mu^{\prime}$ or $\mathrm{t} / \mu \longrightarrow \mathrm{t}^{\prime} / \mu^{\prime}$ holds, then we say that the configuration $\mathrm{t} / \mu$ reduces to the configuration $\mathrm{t}^{\prime} / \mu^{\prime}$; the ambiguity involved in this definition is benign. If $t / \mu \longrightarrow t^{\prime} / \mu$ holds for every store $\mu$, then we write $\mathrm{t} \longrightarrow \mathrm{t}^{\prime}$ and say that the reduction is pure.

The key reduction rule is $\mathrm{R}$-BETA, which states that a function application $(\lambda z . t) v$ reduces to the function body, namely $t$, where every occurrence of the formal argument $z$ has been replaced with the actual argument $v$. The $\lambda$ construct, which prevented the function body t from being evaluated, disappears, so the new term may (in general) be further reduced. Because ML-the-calculus adopts a call-by-value strategy, rule R-BETA is applicable only if the actual argument is a value v. In other words, a function cannot be invoked until its actual argument has been fully evaluated. Rule R-LET is very similar to $\mathrm{R}$-BETA. Indeed, it specifies that let $\mathrm{z}=\mathrm{v}$ in $\mathrm{t}$ has the same behavior, with respect to reduction, as $(\lambda z . t) v$. We remark that substitution of a value for a program variable throughout a term is expensive, so R-BETA and R-LET are never implemented literally: they are only a simple specification. Actual implementations usually employ runtime environments, which may be understood as a form of explicit substitutions (Abadi, Cardelli, Curien, and Lévy, 1991). Please note that our choice of a call-by-value reduction strategy is fairly arbitrary, and has essentially no impact on the type system; the programming language Haskell (Hudak, Peyton Jones, Wadler, Boutel, Fairbairn, Fasel, Guzman, Hammond, Hughes, Johnsson, Kieburtz,

Nikhil, Partain, and Peterson, 1992), whose reduction strategy is known as lazy or call-by-need, also relies on Hindley and Milner's type discipline.

Rule R-DELTA describes the semantics of constants. It merely states that a certain relation $\xrightarrow{\delta}$ is a subset of $\longrightarrow$. Of course, since the set of constants is unspecified, the relation $\xrightarrow{\delta}$ must be kept abstract as well. We require that, if $\mathrm{t} / \mu \xrightarrow{\delta} \mathrm{t}^{\prime} / \mu^{\prime}$ holds, then

(i) $\mathrm{t}$ is of the form $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{n}$, where $\mathrm{c}$ is a destructor of arity $n$; and

(ii) $\operatorname{dom}(\mu)$ is a subset of $\operatorname{dom}\left(\mu^{\prime}\right)$.

Condition (i) ensures that $\delta$-reduction concerns full applications of destructors only, and that these are evaluated in accordance with the call-by-value strategy. Condition (ii) ensures that $\delta$-reduction may allocate new memory locations, but not deallocate existing locations. In particular, a "garbage collection" operator, which destroys unreachable memory cells, cannot be made available as a constant. Doing so would not make much sense anyway in the presence of R-EXTEND, which states that any valid reduction is also valid in a larger store. Condition (ii) allows proving that, if $t / \mu$ reduces to $t^{\prime} / \mu^{\prime}$, then $\operatorname{dom}(\mu)$ is a subset of $\operatorname{dom}\left(\mu^{\prime}\right)$; this is left as an exercise to the reader.

1.2.4 Example [Integers, Continued]: The operational semantics of integer addition may be defined as follows:

$$
\begin{equation*}
\hat{k}_{1} \hat{+} \hat{k}_{2} \xrightarrow{\delta} \widehat{k_{1}+k_{2}} \tag{R-ADD}
\end{equation*}
$$

The left-hand term is the double application $\hat{+} \hat{k}_{1} \hat{k}_{2}$, while the right-hand term is the integer literal $\hat{k}$, where $k$ is the sum of $k_{1}$ and $k_{2}$. The distinction between object level and meta level (that is, between $\hat{k}$ and $k$ ) is needed here to avoid ambiguity.

1.2.5 Example [Pairs, continued]: In addition to the pair constructor defined in Example 1.2.3, we may introduce two destructors $\pi_{1}$ and $\pi_{2}$ of arity 1 . We may define their operational semantics as follows, for $i \in\{1,2\}$ :

$$
\begin{equation*}
\pi_{i}\left(\mathrm{v}_{1}, \mathrm{v}_{2}\right) \xrightarrow{\delta} \mathrm{v}_{i} \tag{R-PROJ}
\end{equation*}
$$

Thus, our treatment of constants is general enough to account for pair construction and destruction; we need not build these features explicitly into the language.

1.2.6 Exercise [Booleans, Recommended, $\star \star$ ]: Let true and false be nullary constructors. Let if be a ternary destructor. Extend the operational semantics with

$$
\begin{equation*}
\text { if true } \mathrm{v}_{1} \mathrm{v}_{2} \xrightarrow{\delta} \mathrm{v}_{1} \tag{R-TRUE}
\end{equation*}
$$

$$
\begin{equation*}
\text { if false } \mathrm{v}_{1} \mathrm{v}_{2} \xrightarrow{\delta} \mathrm{v}_{2} \tag{R-FALSE}
\end{equation*}
$$

Let us use the syntactic sugar if $t_{0}$ then $t_{1}$ else $t_{2}$ for the triple application of if $t_{0} t_{1} t_{2}$. Explain why these definitions do not quite provide the expected behavior. Without modifying the semantics of if, suggest a new definition of the syntactic sugar if $t_{0}$ then $t_{1}$ else $t_{2}$ that corrects the problem.

1.2.7 Example [Sums]: Booleans may in fact be viewed as a special case of the more general concept of sum. Let $i n j_{1}$ and $i n j_{2}$ be unary constructors, called respectively left and right injections. Let case be a ternary destructor, whose semantics is defined as follows, for $i \in\{1,2\}$ :

$$
\begin{equation*}
\operatorname{case}\left(\mathrm{inj}_{i} \mathrm{v}\right) \mathrm{v}_{1} \mathrm{v}_{2} \xrightarrow{\delta} \mathrm{v}_{i} \mathrm{v} \tag{R-CASE}
\end{equation*}
$$

Here, the value $i n j_{i} \mathrm{v}$ is being scrutinized, while the values $\mathrm{v}_{1}$ and $\mathrm{v}_{2}$, which are typically functions, represent the two arms of a standard case construct. The rule selects an appropriate arm (here, $\mathrm{v}_{i}$ ) based on whether the value under scrutiny was formed using a left or right injection. The arm $\mathrm{v}_{i}$ is executed and given access to the data carried by the injection (here, v).

1.2.8 EXERcISE $[\boldsymbol{\star}, \nrightarrow]$ : Explain how to encode true, $f$ al se and the if construct in terms of sums. Check that the behavior of R-TRUE and R-FALSE is properly emulated.

1.2.9 ExAmple [REFEREnces]: Let ref and ! be unary destructors. Let $:=$ be a binary destructor. We write $t_{1}:=t_{2}$ for the double application $:=t_{1} t_{2}$. Define the operational semantics of these three destructors as follows:

$$
\begin{array}{rr}
\text { ref } \mathrm{v} / \varnothing \xrightarrow{\delta} m /(m \mapsto \mathrm{v}) \text { if } m \text { is fresh for } \mathrm{v} & (\mathrm{R}-\mathrm{REF}) \\
! m /(m \mapsto \mathrm{v}) \xrightarrow{\delta} \mathrm{v} /(m \mapsto \mathrm{v}) & \text { (R-DEREF) } \\
m:=\mathrm{v} /\left(m \mapsto \mathrm{v}_{0}\right) \xrightarrow{\delta} \mathrm{v} /(m \mapsto \mathrm{v}) & \text { (R-AssiGN) } \tag{R-AssiGN}
\end{array}
$$

According to R-REF, evaluating ref $v$ allocates a fresh memory location $m$ and binds $\mathrm{v}$ to it. Because configurations are considered equal up to $\alpha-$ conversion of memory locations, the choice of the name $m$ is irrelevant, provided it is chosen fresh for $\mathrm{v}$, so as to prevent inadvertent capture of the memory locations that appear free within v. By R-DEREF, evaluating $! m$ returns the value bound to the memory location $m$ within the current store. By $\mathrm{R}$-Assign, evaluating $m:=\mathrm{v}$ discards the value $\mathrm{v}_{0}$ currently bound to $m$ and produces a new store where $m$ is bound to v. Here, the value returned by the assignment $m:=\mathrm{v}$ is $\mathrm{v}$ itself; in ML-the-programming-language, it is usually a nullary constructor (), pronounced unit.

1.2.10 EXAmple [REcursion]: Let fix be a binary destructor, whose operational semantics is:

$$
\begin{equation*}
\mathrm{fixv}_{1} \mathrm{v}_{2} \xrightarrow{\delta} \mathrm{v}_{1}\left(\mathrm{fix}_{1}\right) \mathrm{v}_{2} \tag{R-FIX}
\end{equation*}
$$

fix is a fixpoint combinator: it effectively allows recursive definitions of functions. Indeed, the construct letrec $f=\lambda$ z. $_{1}$ in $t_{2}$ provided by MLthe-programming-language may be viewed as syntactic sugar for let $f=$ fix $\left(\lambda f . \lambda z . t_{1}\right)$ in $t_{2}$.

Rule R-CONTEXT completes the definition of the operational semantics by defining $\longrightarrow$, a relation between closed configurations, in terms of $\longrightarrow$. The rule states that reduction may take place not only at the term's root, but also deep inside it, provided the path from the root to the point where reduction occurs forms an evaluation context. This is how evaluation contexts determine an evaluation strategy. As a purely technical point, because $\longrightarrow$ relates closed configurations only, we do not need to require that the memory locations in $\operatorname{dom}\left(\mu^{\prime} \backslash \mu\right)$ be fresh for $\mathcal{E}$ : indeed, every memory location that appears within $\mathcal{E}$ must be a member of $\operatorname{dom}(\mu)$.

1.2.11 Exercise $[\star \star \star$, Recommended, $\rightarrow$ a $]$ : Assuming the availability of Booleans and conditionals, integer literals, subtraction, multiplication, integer comparison, and a fixpoint combinator, most of which were defined in previous examples, define a function that computes the factorial of its integer argument, and apply it to $\hat{3}$. Determine, step by step, how this expression reduces to a value.

It is straightforward to check that, if $t / \mu$ reduces to $t^{\prime} / \mu^{\prime}$, then $t$ is not a value. In other words, values are irreducible: they represent a completed computation. The proof is left as an exercise to the reader. The converse, however, does not hold: if $t / \mu$ is irreducible with respect to $\longrightarrow$, then $t$ is not necessarily a value. In that case, the configuration $t / \mu$ is said to be stuck. It represents a runtime error, that is, a situation that does not allow computation to proceed, yet is not considered a valid outcome. A closed source program $\mathrm{t}$ is said to go wrong if and only if the configuration $\mathrm{t} / \varnothing$ reduces to a stuck configuration.

1.2.12 ExAmple: Runtime errors typically arise when destructors are applied to arguments of an unexpected nature. For instance, the expressions $+1 \mathrm{~m}$ and $\pi_{1} \quad 2$ and $! 3$ are stuck, regardless of the current store. The program let $\mathbf{z}=$ $\hat{+} \hat{+}$ in $z$ is not stuck, because $\hat{+} \hat{+}$ is a value. However, its reduct through $\mathrm{R}$-LET is $\hat{+} \hat{+}$, which is stuck, so this program goes wrong. The primary purpose of type systems is to prevent such situations from arising.

1.2.13 Example: The configuration $! m / \mu$ is stuck if $m$ is not in the domain of $\mu$. In that case, however, $! m / \mu$ is not closed. Because we consider $\longrightarrow$ as a relation between closed configurations only, this situation cannot arise. In other
words, the semantics of ML-the-calculus never allows the creation of dangling pointers. As a result, no particular precautions need be taken to guard against them. Several strongly typed programming languages do nevertheless allow dangling pointers in a controlled fashion (Tofte and Talpin, 1997; Crary, Walker, and Morrisett, 1999b; DeLine and Fähndrich, 2001; Grossman, Morrisett, Jim, Hicks, Wang, and Cheney, 2002a).

\section*{Damas and Milner's type system}

ML-the-type-system was originally defined by Milner (1978). Here, we reproduce the definition given a few years later by Damas and Milner (1982), which is written in a more standard style: typing judgements are defined inductively by a collection of typing rules. We refer to this type system as DM.

To begin, we must define types. In DM, like in the simply-typed $\lambda$-calculus, types are first-order terms built out of type constructors and type variables. We begin with several considerations concerning the specification of type constructors.

First, we do not wish to fix the set of type constructors. Certainly, since MLthe-calculus has functions, we need to be able to form an arrow type $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$ out of arbitrary types $\mathrm{T}$ and $\mathrm{T}^{\prime}$; that is, we need a binary type constructor $\rightarrow$. However, because ML-the-calculus includes an unspecified set of constants, we cannot say much else in general. If constants include integer literals and integer operations, as in Example 1.2.1, then a nullary type constructor int is needed; if they include pair construction and destruction, as in Examples 1.2.3 and 1.2.5, then a binary type constructor $\times$ is needed; and so on.

Second, it is common to refer to the parameters of a type constructor by position, that is, by numeric index. For instance, when one writes $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$, it is understood that the type constructor $\rightarrow$ has arity 2, that $\mathrm{T}$ is its first parameter, known as its domain, and that $\mathrm{T}^{\prime}$ is its second parameter, known as its codomain. Here, however, we refer to parameters by names, known as directions. For instance, we define two directions domain and codomain and let the type constructor $\rightarrow$ have arity $\{$ domain, codomain $\}$. The extra generality afforded by directions is exploited in the definition of nonstructural subtyping (Example 1.3.9) and in the definition of rows (Section 1.11).

Last, we allow types to be classified using kinds. As a result, every type constructor must come not only with an arity, but with a richer signature, which describes the kinds of the types to which it is applicable and the kind of the type that it produces. A distinguished kind $\star$ is associated with "normal" types, that is, types that are directly ascribed to expressions and values. For instance, the signature of the type constructor $\rightarrow$ is $\{$ domain $\mapsto \star$, codomain $\mapsto \star\} \Rightarrow \star$, because it is applicable to two "normal" types and produces a "normal" type.

Introducing kinds other than $\star$ allows viewing some terms as ill-formed types; this is illustrated, for instance, in Section 1.11. In the simplest case, however, $\star$ is really the only kind, so the signature of a type constructor is nothing but its arity (a set of directions), and every term is a well-formed type, provided every application of a type constructor respects its arity.

1.2.14 Definition: Let $d$ range over a finite or denumerable set of directions. Let $\kappa$ range over a finite or denumerable set of kinds. Let $\star$ be a distinguished kind. Let $K$ range over partial mappings from directions to kinds. Let $F$ range over a finite or denumerable set of type constructors, each of which has a signature of the form $K \Rightarrow \kappa$. The domain of $K$ is referred to as the arity of $F$, while $\kappa$ is referred to as its image kind. We write $\kappa$ instead of $K \Rightarrow \kappa$ when $K$ is empty. Let $\rightarrow$ be a type constructor of signature $\{$ domain $\mapsto \star$, codomain $\mapsto \star\} \Rightarrow \star$.

The type constructors and their signatures collectively form a signature $\mathcal{S}$. In the following, we assume that a fixed signature $\mathcal{S}$ is given and that every type constructor in it has finite arity, so as to ensure that types are machine representable. However, in Section 1.11, we shall explicitly work with several distinct signatures, some of which involve type constructors of denumerable arity.

A type variable is a name that is used to stand for a type. For simplicity, we assume that every type variable is branded with a kind, or, in other words, that type variables of distinct kinds are drawn from disjoint sets. Each of these sets of type variables is individually subject to $\alpha$-conversion: that is, renamings must preserve kinds. Attaching kinds to type variables is only a technical convenience: in practice, every operation performed during type inference preserves the property that every type is well-kinded, so it is not necessary to keep track of the kind of every type variable. It is only necessary to check that all types supplied by the user, within type declarations, type annotations, or module interfaces, are well-kinded.

1.2.15 Definition: For every kind $\kappa$, let $\mathcal{V}_{\kappa}$ be a disjoint, denumerable set of type variables. Let $\mathrm{X}, \mathrm{Y}$, and $\mathrm{Z}$ range over the set $\mathcal{V}$ of all type variables. Let $\overline{\mathrm{X}}$ and $\bar{Y}$ range over finite sets of type variables. We write $\bar{X} \bar{Y}$ for the set $\bar{X} \cup \bar{Y}$ and often write $\mathrm{X}$ for the singleton set $\{\mathrm{X}\}$. We write $f t v(o)$ for the set of free type variables of an object $o$.

The set of types, ranged over by $\mathrm{T}$, is the free many-kinded term algebra that arises out of the type constructors and type variables.

1.2.16 Definition: A type of kind $\kappa$ is either a member of $\mathcal{V}_{\kappa}$, or a term of the form $F\left\{d_{1} \mapsto \mathrm{T}_{1}, \ldots, d_{n} \mapsto \mathrm{T}_{n}\right\}$, where $F$ has signature $\left\{d_{1} \mapsto \kappa_{1}, \ldots, d_{n} \mapsto \kappa_{n}\right\} \Rightarrow$ $\kappa$ and $\mathrm{T}_{1}, \ldots, \mathrm{T}_{n}$ are types of kind $\kappa_{1}, \ldots, \kappa_{n}$, respectively.

As a notational convention, we assume that, for every type constructor $F$, the directions that form the arity of $F$ are implicitly ordered, so that we may say that $F$ has signature $\kappa_{1} \otimes \ldots \otimes \kappa_{n} \Rightarrow \kappa$ and employ the syntax $F \mathrm{~T}_{1} \ldots \mathrm{T}_{n}$ for applications of $F$. Applications of the type constructor $\rightarrow$ are written infix and associate to the right, so $\mathrm{T} \rightarrow \mathrm{T}^{\prime} \rightarrow \mathrm{T}^{\prime \prime}$ stands for $\mathrm{T} \rightarrow\left(\mathrm{T}^{\prime} \rightarrow \mathrm{T}^{\prime \prime}\right)$.

In order to give meaning to the free type variables of a type, or, more generally, of a typing judgement, traditional presentations of ML-the-typesystem, including Damas and Milner's, employ type substitutions. Most of our presentation avoids substitutions and uses constraints instead. However, we do need substitutions on a few occasions, especially when relating our presentation to Damas and Milner's.

1.2.17 Definition: A type substitution $\theta$ is a total, kind-preserving mapping of type variables to types that is the identity everywhere but on a finite subset of $\mathcal{V}$, which we call the domain of $\theta$ and write $\operatorname{dom}(\theta)$. The range of $\theta$, which we write range $(\theta)$, is the set $\operatorname{ftv}(\theta(\operatorname{dom}(\theta)))$. A type substitution may naturally be viewed as a total, kind-preserving mapping of types to types. In the following, we write $\overline{\mathrm{X}} \# \theta$ for $\overline{\mathrm{X}} \#(\operatorname{dom}(\theta) \cup$ range $(\theta))$. We write $\theta \backslash \overline{\mathrm{X}}$ for the restriction of $\theta$ outside $\overline{\mathrm{X}}$, that is, the restriction of $\theta$ to $\mathcal{V} \backslash \overline{\mathrm{X}}$. We sometimes let $\varphi$ denote a type substitution.

If $\vec{X}$ and $\vec{T}$ are respectively a vector of distinct type variables and a vector of types of the same (finite) length, such that, for every index $i, \mathrm{x}_{i}$ and $\mathrm{T}_{i}$ have the same kind, then $[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}]$ denotes the substitution that maps $\mathrm{X}_{i}$ to $\mathrm{T}_{i}$ for every index $i$. The domain of $[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}]$ is a subset of $\overline{\mathrm{X}}$, the set underlying the vector $\overrightarrow{\mathrm{X}}$. Its range is a subset of $f t v(\overline{\mathrm{T}})$, where $\overline{\mathrm{T}}$ is the set underlying the vector $\vec{T}$. Every substitution $\theta$ may be written under the form $[\vec{X} \mapsto \vec{T}]$, where $\overline{\mathrm{X}}=\operatorname{dom}(\theta)$. Then, $\theta$ is idempotent if and only if $\overline{\mathrm{X}} \# \mathrm{ftv}(\overline{\mathrm{T}})$ holds.

As pointed out earlier, types are first-order terms; that is, in the grammar of types, none of the productions binds a type variable. As a result, every type variable that appears within a type $\mathrm{T}$ appears free within $\mathrm{T}$. This situation is identical to that of the simply-typed $\lambda$-calculus. Things become more interesting when we introduce type schemes. As its name implies, a type scheme may describe an entire family of types; this effect is achieved via universal quantification over a set of type variables.

1.2.18 Definition: A type scheme $\mathrm{S}$ is an object of the form $\forall \overline{\mathrm{X}}$. $\mathrm{T}$, where $\mathrm{T}$ is a type of kind $\star$ and the type variables $\overline{\mathrm{X}}$ are considered bound within $\mathrm{T}$.

One may view the type $\mathrm{T}$ as the trivial type scheme $\forall \varnothing$. $\mathrm{T}$, where no type variables are universally quantified, so types may be viewed as a subset of type schemes. The type scheme $\forall \bar{X} . T$ may be viewed as a finite way of describing the possibly infinite family of types of the form $[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$, where $\overrightarrow{\mathrm{T}}$ is arbitrary.

\begin{tabular}{|c|c|c|c|c|}
\hline$\Gamma(\mathrm{x})=\mathrm{S}$ & \multirow{2}{*}{$(\mathrm{DM}-\mathrm{VAR})$} & $\Gamma \vdash \mathrm{t}_{1}: \mathrm{s}$ & $\Gamma ; \mathrm{z}: \mathrm{S} \vdash \mathrm{t}_{2}: \mathrm{T}$ & \multirow{2}{*}{ (DM-LET) } \\
\hline$\overline{\Gamma \vdash \mathrm{x}: \mathrm{S}}$ & & \multicolumn{2}{|c|}{$\overline{\Gamma \vdash \text { let } z=t_{1} \text { in } t_{2}: T}$} & \\
\hline$\Gamma ; \mathrm{z}: \mathrm{T} \vdash \mathrm{t}: \mathrm{T}^{\prime}$ & \multirow{2}{*}{$(\mathrm{DM}-\mathrm{ABS})$} & $\Gamma \vdash \mathrm{t}: \mathrm{T}$ & $\overline{\mathrm{x}} \# \mathrm{ftv}(\Gamma)$ & \multirow{2}{*}{ (DM-GEN) } \\
\hline$\overline{\Gamma \vdash \lambda z . t: \mathrm{T} \rightarrow \mathrm{T}^{\prime}}$ & & \multirow{3}{*}{\multicolumn{2}{|c|}{\begin{tabular}{c}
$\Gamma \vdash \mathrm{t}: \forall \mathrm{X} . \mathrm{T}$ \\
$\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{X}} . \mathrm{T}$ \\
$\Gamma \vdash \mathrm{t}:[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$
\end{tabular}}} & \\
\hline ![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-015.jpg?height=73\&width=453\&top_left_y=490\&top_left_x=312) & \multirow{2}{*}{ (DM-APP) } & & & \multirow{2}{*}{ (DM-INST) } \\
\hline$\Gamma \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}$ & & & & \\
\hline
\end{tabular}

Figure 1-3: Typing rules for DM

Such types are called instances of the type scheme $\forall \bar{X}$.T. Note that, throughout most of this chapter, we work with constrained type schemes, a generalization of DM type schemes (Definition 1.3.2).

Typing environments, or environments for short, are used to collect assumptions about an expression's free identifiers.

1.2.19 Definition: An environment $\Gamma$ is a finite ordered sequence of pairs of a program identifier and a type scheme. We write $\varnothing$ for the empty environment and ; for the concatenation of environments. An environment may be viewed as a finite mapping from program identifiers to type schemes by letting $\Gamma(\mathrm{x})=\mathrm{S}$ if and only if $\Gamma$ is of the form $\Gamma_{1} ; \mathrm{x}: \mathrm{S} ; \Gamma_{2}$, where $\Gamma_{2}$ contains no assumption about $\mathrm{x}$. The set of defined program identifiers of an environment $\Gamma$, written $d p i(\Gamma)$, is defined by $d p i(\varnothing)=\varnothing$ and $d p i(\Gamma ; \mathrm{x}: \mathrm{S})=d p i(\Gamma) \cup\{\mathrm{x}\}$.

To complete the definition of Damas and Milner's type system, there remains to define typing judgements. A typing judgement takes the form $\Gamma \vdash \mathrm{t}: \mathrm{S}$, where $\mathrm{t}$ is an expression of interest, $\Gamma$ is an environment, which typically contains assumptions about t's free program identifiers, and $\mathrm{S}$ is a type scheme. Such a judgement may be read: under assumptions $\Gamma$, the expression $\mathrm{t}$ has the type scheme $\mathrm{S}$. By abuse of language, it is sometimes said that $\mathrm{t}$ has type $\mathrm{S}$. A typing judgement is valid (or holds) if and only if it may be derived using the rules that appear in Figure 1-3. An expression t is well-typed within the environment $\Gamma$ if and only if some judgement of the form $\Gamma \vdash t: S$ holds; it is ill-typed within $\Gamma$ otherwise.

Rule DM-VAR allows fetching a type scheme for an identifier $\mathrm{x}$ from the environment. It is equally applicable to program variables, memory locations, and constants. If no assumption concerning $\mathrm{x}$ appears in the environment $\Gamma$, then the rule isn't applicable. In that case, the expression $x$ is ill-typed within $\Gamma$ - can you prove it? Assumptions about constants are usually collected in
a so-called initial environment $\Gamma_{0}$. It is the environment under which closed programs are typechecked, so every subexpression is typechecked under some extension $\Gamma$ of $\Gamma_{0}$. Of course, the type schemes assigned by $\Gamma_{0}$ to constants must be consistent with their operational semantics; we say more about this later (Section 1.7). Rule DM-ABS specifies how to typecheck a $\lambda$-abstraction $\lambda$ z.t. Its premise requires the body of the function, namely $t$, to be well-typed under an extra assumption, which causes all free occurrences of $z$ within $t$ to receive a common type $\mathrm{T}$. Its conclusion forms the arrow type $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$ out of the types of the function's formal parameter, namely $\mathrm{T}$, and result, namely $\mathrm{T}^{\prime}$. It is worth noting that this rule always augments the environment with a type $\mathrm{T}$ - recall that, by convention, types form a subset of type schemesbut never with a nontrivial type scheme. DM-APP states that the type of a function application is the codomain of the function's type, provided that the domain of the function's type is a valid type for the actual argument. DMLET closely mirrors the operational semantics: whereas the semantics of the local definition let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}$ is to augment the runtime environment by binding $\mathrm{z}$ to the value of $\mathrm{t}_{1}$ prior to evaluating $\mathrm{t}_{2}$, the effect of DM-LET is to augment the typing environment by binding $\mathrm{z}$ to a type scheme for $t_{1}$ prior to typechecking $t_{2}$. DM-GEN turns a type into a type scheme by universally quantifying over a set of type variables that do not appear free in the environment; this restriction is discussed in Example 1.2.20 below. DMINST, on the contrary, turns a type scheme into one of its instances, which may be chosen arbitrarily. These two operations are referred to as generalization and instantiation. The notion of type scheme and the rules DM-GEN and DMINsT are characteristic of ML-the-type-system: they distinguish it from the simply-typed $\lambda$-calculus.

1.2.20 EXAmPLE: It is unsound to allow generalizing type variables that appear free in the environment. For instance, consider the typing judgement $\mathbf{z}: \mathrm{X} \vdash \mathbf{z}$ : X (1), which, according to DM-VAR, is valid. Applying an unrestricted version of DM-GEN to it, we obtain $\mathrm{z}: \mathrm{X} \vdash \mathrm{z}: \forall \mathrm{X} . \mathrm{X}$ (2), whence, by DM-INST, z : X $\vdash$ z : Y (3). By DM-ABS and DM-GEN, we then have $\varnothing \vdash \lambda z . z: \forall X Y . X \rightarrow Y$. In other words, the identity function has unrelated argument and result types! Then, the expression $(\lambda z . z) \hat{0} \hat{0}$, which reduces to the stuck expression $\hat{0} \hat{0}$, has type scheme $\forall z . z$. So, well-typed programs may cause runtime errors: the type system is unsound.

What happened? It is clear that the judgement (1) is correct only because the type assigned to $\mathrm{z}$ is the same in its assumption and in its right-hand side. For the same reason, the judgements (2) and (3)-the former of which may be written $z: X \vdash z: \forall Y . Y$-are incorrect. Indeed, such judgements defeat the very purpose of environments, since they disregard their assumption.

By universally quantifying over $\mathrm{x}$ in the right-hand side only, we break the connection between occurrences of $\mathrm{X}$ in the assumption, which remain free, and occurrences in the right-hand side, which become bound. This is correct only if there are in fact no free occurrences of $\mathrm{X}$ in the assumption.

It is a key feature of ML-the-type-system that DM-ABS may only introduce a type $\mathrm{T}$, rather than a type scheme, into the environment. Indeed, this allows the rule's conclusion to form the arrow type $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$. If instead the rule were to introduce the assumption $\mathrm{z}: \mathrm{S}$ into the environment, then its conclusion would have to form $\mathrm{S} \rightarrow \mathrm{T}^{\prime}$, which is not a well-formed type. In other words, this restriction is necessary to preserve the stratification between types and type schemes. If we were to remove this stratification, thus allowing universal quantifiers to appear deep inside types, we would obtain an implicitly-typed version of System F (TAPL Chapter 23). Type inference for System F is undecidable (Wells, 1999), while type inference for ML-the-type-system is decidable, as we show later, so this design choice has a rather drastic impact.

1.2.21 Exercise [ $\star$, Recommended]: Build a type derivation for the expression $\lambda z_{1}$. let $z_{2}=z_{1}$ in $z_{2}$ within DM.

1.2.22 Exercise $[\star$, Recommended]: Let int be a nullary type constructor of signature $\star$. Let $\Gamma_{0}$ consist of the bindings $\hat{+}:$ int $\rightarrow$ int $\rightarrow$ int and $\hat{k}:$ int, for every integer $k$. Can you find derivations of the following valid typing judgements? Which of these judgements are valid in the simply-typed $\lambda$-calculus, where let $z=t_{1}$ in $t_{2}$ is syntactic sugar for $\left(\lambda z . t_{2}\right) t_{1}$ ?

$$
\begin{gathered}
\Gamma_{0} \vdash \lambda z . z: \operatorname{int} \rightarrow \operatorname{int} \\
\Gamma_{0} \vdash \lambda z . z: \forall x . x \rightarrow x \\
\Gamma_{0} \vdash \text { et } f=\lambda z . z \hat{+} \hat{1} \text { in } f \hat{2}: \operatorname{int} \\
\Gamma_{0} \vdash \text { let } f=\lambda z . z \text { inf } f \hat{2}: \operatorname{int}
\end{gathered}
$$

Show that the expressions $\hat{1} \hat{2}$ and $\lambda f$.(f $f$ ) are ill-typed within $\Gamma_{0}$. Could these expressions be well-typed in a more powerful type system?

1.2.23 EXERCISE $[\star \star \star]$ : In fact, the rules shown in Figure 1-3 are not exactly Damas and Milner's original rules. In (Damas and Milner, 1982), the generalization and instantiation rules are:

$$
\begin{gather*}
\frac{\Gamma \vdash \mathrm{t}: \mathrm{S} \quad \mathrm{X} \notin f t v(\Gamma)}{\Gamma \vdash \mathrm{t}: \forall \mathrm{X} . \mathrm{S}}  \tag{DM-GEN'}\\
\frac{\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{X}} . \mathrm{T} \quad \overline{\mathrm{Y}} \# f t v(\forall \overline{\mathrm{X}} . \mathrm{T})}{\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{Y}} .[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}} \tag{DM-INST'}
\end{gather*}
$$
where $\forall$ X.S stands for $\forall X \bar{X}$.T if $S$ stands for $\forall \bar{X}$.T. Show that the combination of DM-GEN' and DM-INST' is equivalent to the combination of DM-GEN and DM-INST.

DM enjoys a number of nice theoretical properties, which have practical implications. First, under suitable hypotheses about the semantics of constants, about the type schemes that they receive in the initial environment, and - in the presence of side effects - under a slight restriction of the syntax of let constructs, it is possible to show that the type system is sound: that is, well-typed (closed) programs do not go wrong. This essential property ensures that programs that are accepted by the typechecker may be compiled without runtime checks. Furthermore, it is possible to show that there exists an algorithm that, given a (closed) environment $\Gamma$ and a program $t$, tells whether $t$ is well-typed with respect to $\Gamma$, and if so, produces a principal type scheme $\mathrm{S}$. A principal type scheme is such that (i) it is valid, that is, $\Gamma \vdash \mathrm{t}: \mathrm{S}$ holds, and (ii) it is most general, that is, every judgement of the form $\Gamma \vdash t: S^{\prime}$ follows from $\Gamma \vdash \mathrm{t}: \mathrm{S}$ by DM-InsT and DM-GEN. (For the sake of simplicity, we have stated the properties of the type inference algorithm only in the case of a closed environment $\Gamma$; the specification is slightly heavier in the general case.) This implies that type inference is decidable: the compiler does not require expressions to be annotated with types. It also implies that, under a fixed environment $\Gamma$, all of the type information associated with an expression $t$ may be summarized in the form of a single (principal) type scheme, which is very convenient.

\section*{Road map}

Before proving the above claims, we first generalize our presentation by moving to a constraint-based setting. The necessary tools, namely the constraint language, its interpretation, and a number of constraint equivalence laws, are introduced in Section 1.3. In Section 1.4, we describe the standard constraintbased type system $\operatorname{HM}(X)$ (Odersky, Sulzmann, and Wehr, 1999a; Sulzmann, Müller, and Zenger, 1999; Sulzmann, 2000). We prove that, when constraints are made up of equations between free, finite terms, $\operatorname{HM}(X)$ is a reformulation of DM. In the presence of a more powerful constraint language, $\operatorname{HM}(X)$ is an extension of DM. In Section 1.5, we propose an original reformulation of $\operatorname{HM}(X)$, dubbed $\operatorname{PCB}(X)$, whose distinctive feature is to exploit type scheme introduction and instantiation constraints. In Section 1.6, we show that, thanks to the extra expressive power afforded by these constraint forms, type inference may be viewed as a combination of constraint generation and constraint solving, as promised earlier. Indeed, we define a constraint generator and relate it with $\operatorname{PCB}(X)$. Then, in Section 1.7, we give a type soundness
theorem. It is stated purely in terms of constraints, but-thanks to the results developed in the previous sections - applies equally to $\operatorname{PCB}(X), \operatorname{HM}(X)$, and DM.

Throughout this core material, the syntax and interpretation of constraints are left partly unspecified. Thus, the development is parameterized with respect to them-hence the unknown $X$ in the names $\operatorname{HM}(X)$ and $\operatorname{PCB}(X)$. We really describe a family of constraint-based type systems, all of which share a common constraint generator and a common type soundness proof. Constraint solving, however, cannot be independent of $X$ : on the contrary, the design of an efficient solver is heavily dependent on the syntax and interpretation of constraints. In Section 1.8, we consider constraint solving in the particular case where constraints are made up of equations interpreted in a free tree model, and define a constraint solver on top of a standard first-order unification algorithm.

The remainder of this chapter deals with extensions of the framework. In Section 1.9, we explain how to extend ML-the-calculus with a number of features, including data structures, pattern matching, and type annotations. In Section 1.10, we extend the constraint language with universal quantification and describe a number of extra features that require this extension, including a different flavor of type annotations, polymorphic recursion, and first-class universal and existential types. Last, in Section 1.11, we extend the constraint language with rows and describe their applications, which include extensible variants and records.

\subsection*{1.3 Constraints}

In this section, we define the syntax and logical meaning of constraints. Both are partly unspecified. Indeed, the set of type constructors (Definition 1.2.14) must contain at least the binary type constructor $\rightarrow$, but might contain more. Similarly, the syntax of constraints involves a set of so-called predicates on types, which we require to contain at least a binary subtyping predicate $\leq$, but might contain more. Furthermore, the logical interpretation of type constructors and of predicates is left almost entirely unspecified. This freedom allows reasoning not only about Damas and Milner's type system, but also about a family of constraint-based extensions of it.

Type constructors other than $\rightarrow$ and predicates other than $\leq$ will never explicitly appear in the definition of our constraint-based type systems, precisely because the definition is parametric with respect to them. They can (and usually do) appear in the type schemes assigned to constructors and destructors by the initial environment $\Gamma_{0}$.

The introduction of subtyping has little impact on the complexity of our

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-020.jpg?height=566&width=1518&top_left_y=227&top_left_x=241)

Figure 1-4: Syntax of type schemes and constraints

proofs, yet increases the framework's expressive power. When subtyping is not desired, we interpret the predicate $\leq$ as equality.

\section*{Syntax}

We now define the syntax of constrained type schemes and of constraints, and introduce some extra constraint forms as syntactic sugar.

1.3.1 Definition: Let $P$ range over a finite or denumerable set of predicates, each of which has a signature of the form $\kappa_{1} \otimes \ldots \otimes \kappa_{n} \Rightarrow \cdot$, where $n \geq 0$. Let $\leq$ be a distinguished predicate of signature $\star \otimes \star \Rightarrow \bullet$

1.3.2 Definition: The syntax of type schemes and constraints is given in Figure 14. It is further restricted by the following requirements. In the type scheme $\forall \overline{\mathrm{X}}[C] . \mathrm{T}$ and in the constraint $\mathrm{x} \preceq \mathrm{T}$, the type $\mathrm{T}$ must have kind $\star$. In the constraint $P \mathrm{~T}_{1} \ldots \mathrm{T}_{n}$, the types $\mathrm{T}_{1}, \ldots, \mathrm{T}_{n}$ must have kind $\kappa_{1}, \ldots, \kappa_{n}$, respectively, if $P$ has signature $\kappa_{1} \otimes \ldots \otimes \kappa_{n} \Rightarrow \cdot$. We write $\forall \overline{\mathrm{X}}$.T for $\forall \overline{\mathrm{x}}[$ true].T, which allows viewing DM type schemes as a subset of constrained type schemes.

We write $\mathrm{T}_{1} \leq \mathrm{T}_{2}$ for the binary predicate application $\leq \mathrm{T}_{1} \mathrm{~T}_{2}$, and call it a subtyping constraint. By convention, $\exists$ and def bind tighter than $\wedge$; that is, $\exists \overline{\mathrm{x}} . C \wedge D$ is $(\exists \overline{\mathrm{x}} . C) \wedge D$ and def $\mathrm{x}: \sigma$ in $C \wedge D$ is $(\operatorname{def} \mathrm{x}: \sigma$ in $C) \wedge D$. In $\forall \overline{\mathrm{x}}[C] . \mathrm{T}$, the type variables $\overline{\mathrm{X}}$ are bound within $C$ and $\mathrm{T}$. In $\exists \overline{\mathrm{X}}$. $C$, the type variables $\overline{\mathrm{X}}$ are bound within $C$. The sets of free type variables of a type scheme $\sigma$ and of a constraint $C$, written $f t v(\sigma)$ and $f t v(C)$, respectively, are defined accordingly. In def $\mathrm{x}: \sigma$ in $C$, the identifier $\mathrm{x}$ is bound within $C$. The sets
of free program identifiers of a type scheme $\sigma$ and of a constraint $C$, written $f p i(\sigma)$ and $f p i(C)$, respectively, are defined accordingly. Please note that $\mathrm{x}$ occurs free in the constraint $\mathrm{x} \preceq \mathrm{T}$.

We immediately introduce a number of derived constraint forms:

1.3.3 Definition: Let $\sigma$ be $\forall \overline{\mathrm{X}}[C]$.T. If $\overline{\mathrm{X}} \# \operatorname{ftv}\left(\mathrm{T}^{\prime}\right)$ holds, then $\sigma \preceq \mathrm{T}^{\prime}$ (read: $\mathrm{T}^{\prime}$ is an instance of $\sigma)$ stands for the constraint $\exists \overline{\mathrm{X}}$. $\left(C \wedge \mathrm{T} \leq \mathrm{T}^{\prime}\right)$. We write $\exists \sigma$ (read: $\sigma$ has an instance) for $\exists \overline{\mathrm{x}} . C$ and let $\mathrm{x}: \sigma$ in $C$ for $\exists \sigma \wedge \operatorname{def} \mathrm{x}: \sigma$ in $C$.

Constrained type schemes generalize Damas and Milner's type schemes, while our definition of instantiation constraints generalizes Damas and Milner's instance relation (Definition 1.2.18). Let us draw a comparison. First, Damas and Milner's instance relation yields a "yes/no" answer, and is purely syntactic: for instance, the type $\mathrm{Y} \rightarrow \mathrm{Z}$ is not an instance of $\forall \mathrm{X}$. $\mathrm{X} \rightarrow \mathrm{X}$ in Damas and Milner's sense, because $\mathrm{Y}$ and $\mathrm{Z}$ are distinct type variables. In our presentation, on the other hand, $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X} \preceq \mathrm{Y} \rightarrow \mathrm{Z}$ is not an assertion; rather, it is a constraint, which by definition is $\exists \mathrm{X}$. (true $\wedge \mathrm{X} \rightarrow \mathrm{X} \leq \mathrm{Y} \rightarrow \mathrm{Z}$ ). We later prove that it is equivalent to $\exists \mathrm{X}$. $(\mathrm{Y} \leq \mathrm{X} \wedge \mathrm{X} \leq \mathrm{Z})$ and to $\mathrm{Y} \leq \mathrm{Z}$, or, if subtyping is interpreted as equality, to $\mathrm{Y}=\mathrm{Z}$. That is, $\sigma \preceq \mathrm{T}^{\prime}$ represents a condition on (the types denoted by) the type variables in $f t v\left(\sigma, \mathrm{T}^{\prime}\right)$ for $\mathrm{T}^{\prime}$ to be an instance of $\sigma$, in a logical, rather than purely syntactic, sense. Second, the definition of instantiation constraints involves subtyping, so as to ensure that any supertype of an instance of $\sigma$ is again an instance of $\sigma$ (see rule C-ExTrans in Figure 1-6 and Lemma 1.3.17). This is consistent with the purpose of subtyping, which is to allow supplying a subtype where a supertype is expected (TAPL Chapter 15). Third and last, every type scheme now carries a constraint. The constraint $C$, whose free type variables may or may not be members of $\overline{\mathrm{x}}$, restricts the instances of the type scheme $\forall \overline{\mathrm{x}}[C]$.T. This is expressed in the instantiation constraint $\exists \overline{\mathrm{X}}$. $\left(C \wedge \mathrm{T} \leq \mathrm{T}^{\prime}\right)$, where the values that $\overline{\mathrm{X}}$ may assume are restricted by the requirement that $C$ be satisfied. This requirement vanishes in the case of DM type schemes, where $C$ is true. Our notions of constrained type scheme and of instantiation constraint are standard: they are exactly those of $\operatorname{HM}(X)$ (Odersky, Sulzmann, and Wehr, 1999a).

The constraint true, which is always satisfied, mainly serves to indicate the absence of a nontrivial constraint, while false, which has no solution, may be understood as the indication of a type error. Composite constraints include conjunction and existential quantification, which have their standard meaning, as well as type scheme introduction and type scheme instantiation constraints, which are similar to Gustavsson and Svenningsson's constraint abstractions (2001b). In short, the construct def $\mathrm{x}: \sigma$ in $C$ binds the name $\mathrm{x}$ to the type scheme $\sigma$ within the constraint $C$. If $C$ contains a subconstraint of
the form $\mathrm{x} \preceq \mathrm{T}$, where this occurrence of $\mathrm{x}$ is free in $C$, then this subconstraint acquires the meaning $\sigma \preceq \mathrm{T}$. Thus, the constraint $\mathrm{x} \preceq \mathrm{T}$ is indeed an instantiation constraint, where the type scheme that is being instantiated is referred to by name. The constraint def $\mathrm{x}: \sigma$ in $C$ may be viewed as an explicit substitution of the type scheme $\sigma$ for the name x within $C$. Later (Section 1.5), we use such explicit substitutions to supplant typing environments. That is, where Damas and Milner's type system augments the current typing environment (DM-ABS, DM-LET), we introduce a new def binding in the current constraint; where it looks up the current typing environment (DM-VAR), we employ an instantiation constraint. The point is that it is then up to a constraint solver to choose a strategy for reducing explicit substitutions-for instance, one might wish to simplify $\sigma$ before substituting it for $\mathrm{x}$ within $C$-whereas the use of environments in standard type systems such as DM and $\mathrm{HM}(X)$ imposes an eager substitution strategy, which is inefficient and thus never literally implemented. The use of type scheme introduction and instantiation constraints allows separating constraint generation and constraint solving without compromising efficiency, or, in other words, without introducing a gap between the description of the type inference algorithm and its actual implementation. Although the algorithm that we plan to describe is not new, its description in terms of constraints is: to the best of our knowledge, the only close relative of our def constraints is to be found in (Gustavsson and Svenningsson, 2001b). Fähndrich, Rehof, and Das's instantiation constraints (2000) are also related, but may be recursive and are meant to be solved using a semi-unification procedure, as opposed to a unification algorithm extended with facilities for creating and instantiating type schemes, as in our case.

One consequence of introducing constraints inside type schemes is that some type schemes have no instances at all, or have instances only if a certain constraint holds. For instance, the type scheme $\sigma=\forall x[$ bool $=$ int].X, where the nullary type constructors int and bool have distinct interpretations, has no instances; that is, no constraint of the form $\sigma \preceq \mathrm{T}^{\prime}$ has a solution. The type scheme $\sigma=\forall \mathrm{Z}[\mathrm{X}=\mathrm{Y} \rightarrow \mathrm{Z}] . \mathrm{Z}$ has an instance only if $\mathrm{X}=\mathrm{Y} \rightarrow \mathrm{Z}$ holds for some Z; in other words, for every $\mathrm{T}^{\prime}, \sigma \preceq \mathrm{T}^{\prime}$ entails $\exists \mathrm{Z}$. $(\mathrm{X}=\mathrm{Y} \rightarrow \mathrm{Z})$. (We define entailment on page 29.) We later prove that the constraint $\exists \sigma$ is equivalent to $\exists \mathrm{Z} . \sigma \preceq \mathrm{Z}$, where $\mathrm{Z} \notin f t v(\sigma)$ (Exercise 1.3.23). That is, $\exists \sigma$ expresses the requirement that $\sigma$ have an instance. Type schemes that do not have an instance indicate a type error, so in many situations, one wishes to avoid them; for this reason, we often use the constraint form let $\mathrm{x}: \sigma$ in $C$, which requires $\sigma$ to have an instance and at the same time associates it with the name $\mathrm{x}$. Because the def form is more primitive, it is easier to work with at a low level, but it is no longer explicitly used after Section 1.3; we always use let instead.

1.3.4 Definition: Environments $\Gamma$ remain as in Definition 1.2.19, except DM type schemes S are replaced with constrained type schemes $\sigma$. We write $d f p i(\Gamma)$ for $d p i(\Gamma) \cup f p i(\Gamma)$. We define def $\varnothing$ in $C=C$ and $\operatorname{def} \Gamma ; \mathrm{x}: \sigma$ in $C=$ def $\Gamma$ in def $\mathrm{x}: \sigma$ in $C$. Similarly, we define let $\varnothing$ in $C=C$ and let $\Gamma ; \mathrm{x}$ : $\sigma$ in $C=$ let $\Gamma$ in let $\mathrm{x}: \sigma$ in $C$. We define $\exists \varnothing=$ true and $\exists(\Gamma ; \mathrm{x}: \sigma)=$ $\exists \Gamma \wedge \operatorname{def} \Gamma$ in $\exists \sigma$.

In order to establish or express certain laws of equivalence between constraints, we need constraint contexts. A context is a constraint with zero, one, or several holes, written []. The syntax of contexts is as follows:

$$
\mathcal{C}::=\square|C| \mathcal{C} \wedge \mathcal{C}|\exists \overline{\mathrm{x}} . \mathcal{C}| \operatorname{def} \mathrm{x}: \sigma \text { in } \mathcal{C} \mid \operatorname{def} \mathrm{x}: \forall \overline{\mathrm{x}}[\mathcal{C}] . \mathrm{T} \text { in } C
$$

The application of a constraint context $\mathcal{C}$ to a constraint $C$, written $\mathcal{C}[C]$, is defined in the usual way. Because a context may have any number of holes, $C$ may disappear or be duplicated in the process. Because a hole may appear in the scope of a binder, some of $C$ 's free type variables and free program identifiers may become bound in $\mathcal{C}[C]$. We write $\operatorname{dtv}(\mathcal{C})$ and $\operatorname{dpi}(\mathcal{C})$ for the sets of type variables and program identifiers, respectively, that $\mathcal{C}$ may thus capture. We write let $\mathrm{x}: \forall \overline{\mathrm{x}}[\mathcal{C}] . T$ in $C$ for $\exists \overline{\mathrm{x}} . \mathcal{C} \wedge \operatorname{def} \mathrm{x}: \forall \overline{\mathrm{x}}[\mathcal{C}] . T$ in $C$. Being able to state such a definition is why we require multi-hole contexts. We let range over existential constraint contexts, defined by $\mathcal{X}::=[] \mid \exists \overline{\mathrm{X}} . \mathcal{X}$.

\section*{Meaning}

We have defined the syntax of constraints and given an informal description of their meaning. We now give a formal definition of the interpretation of constraints. We begin with the definition of a model:

1.3.5 Definition: For every kind $\kappa$, let $\mathcal{M}_{\kappa}$ be a nonempty set, whose elements are the ground types of kind $\kappa$. In the following, $t$ ranges over $\mathcal{M}_{\kappa}$, for some $\kappa$ that may be determined from the context. For every type constructor $F$ of signature $K \Rightarrow \kappa$, let $F$ denote a total function from $\mathcal{M}_{K}$ into $\mathcal{M}_{\kappa}$, where the indexed product $\mathcal{M}_{K}$ is the set of all mappings of domain $\operatorname{dom}(K)$ that map every $d \in \operatorname{dom}(K)$ to an element of $\mathcal{M}_{K(d)}$. For every predicate $P$ of signature $\kappa_{1} \otimes \ldots \otimes \kappa_{n} \Rightarrow \cdot$, let $P$ denote a predicate on $\mathcal{M}_{\kappa_{1}} \times \ldots \times \mathcal{M}_{\kappa_{n}}$. We require the predicate $\leq$ on $\mathcal{M}_{\star} \times \mathcal{M}_{\star}$ to be a partial order.

For the sake of convenience, we abuse notation and write $F$ for both the type constructor and its interpretation; similarly for predicates. We freely assume that a binary equality predicate, whose interpretation is equality on $\mathcal{M}_{\kappa}$, is available at every kind $\kappa$, so $\mathrm{T}_{1}=\mathrm{T}_{2}$, where $\mathrm{T}_{1}$ and $\mathrm{T}_{2}$ have kind $\kappa$, is a well-formed constraint.

By varying the set of type constructors, the set of predicates, the set of ground types, and the interpretation of type constructors and predicates, one may define an entire family of related type systems. We informally refer to the collection of these choices as $X$. Thus, the type systems $\operatorname{HM}(X)$ and $\operatorname{PCB}(X)$, described in Sections 1.4 and 1.5, are parameterized by $X$.

The following examples give standard ways of defining the set of ground types and the interpretation of type constructors.

1.3.6 Example [Syntactic models]: For every kind $\kappa$, let $\mathcal{M}_{\kappa}$ consist of the closed types of kind $\kappa$. Then, ground types are types that do not have any free type variables, and form the so-called Herbrand universe. Let every type constructor $F$ be interpreted as itself. Models that define ground types and interpret type constructors in this manner are referred to as syntactic.

1.3.7 EXAmple [TREe models]: Let a path $\pi$ be a finite sequence of directions. The empty path is written $\epsilon$ and the concatenation of the paths $\pi$ and $\pi^{\prime}$ is written $\pi \cdot \pi^{\prime}$. Let a tree be a partial function $t$ from paths to type constructors whose domain is nonempty and prefix-closed and such that, for every path $\pi$ in the domain of $t$, if the type constructor $t(\pi)$ has signature $K \Rightarrow \kappa$, then $\pi \cdot d \in \operatorname{dom}(t)$ is equivalent to $d \in \operatorname{dom}(K)$ and, furthermore, for every $d \in \operatorname{dom}(K)$, the type constructor $t(\pi \cdot d)$ has image kind $K(d)$. If $\pi$ is in the domain of $t$, then the subtree of $t$ rooted at $\pi$, written $t / \pi$, is the partial function $\pi^{\prime} \mapsto t\left(\pi \cdot \pi^{\prime}\right)$. A tree is finite if and only if it has finite domain. A tree is regular if and only if it has a finite number of distinct subtrees. Every finite tree is thus regular. Let $\mathcal{M}_{\kappa}$ consist of the finite (resp. regular) trees $t$ such that $t(\epsilon)$ has image kind $\kappa$ : then, we have a finite (resp. regular) tree model.

If $F$ has signature $K \Rightarrow \kappa$, one may interpret $F$ as the function that maps $T \in \mathcal{M}_{K}$ to the ground type $t \in \mathcal{M}_{\kappa}$ defined by $t(\epsilon)=F$ and $t / d=T(d)$ for $d \in \operatorname{dom}(T)$, that is, the unique ground type whose head symbol is $F$ and whose subtree rooted at $d$ is $T(d)$. Then, we have a free tree model. Please note that free finite tree models coincide with syntactic models, as defined in the previous example.

Rows (Section 1.11) are interpreted in a tree model, albeit not a free one. The following examples suggest different ways of interpreting the subtyping predicate.

1.3.8 EXample [Equality models]: The simplest way of interpreting the subtyping predicate is to let $\leq$ denote equality on every $\mathcal{M}_{\kappa}$. Models that do so are referred to as equality models. When no predicate other than equality is available, we say that the model is equality-only.

1.3.9 Example [StRuctURal, NonstructURal SUbtyping]: Let a variance $\nu$ be a nonempty subset of $\{-,+\}$, written - (contravariant), + (covariant), or $\pm$ (invariant) for short. Define the composition of two variances as an associative commutative operation with + as neutral element and such that $--=+$ and $\pm-= \pm \pm= \pm$. Now, consider a free (finite or regular) tree model, where every direction $d$ comes with a fixed variance $\nu(d)$. Define the variance $\nu(\pi)$ of a path $\pi$ as the composition of the variances of its elements. Let $\leqslant$ be a partial order on type constructors such that (i) if $F_{1} \leqslant F_{2}$ holds and $F_{1}$ and $F_{2}$ have signature $K_{1} \Rightarrow \kappa_{1}$ and $K_{2} \Rightarrow \kappa_{2}$, respectively, then $K_{1}$ and $K_{2}$ agree on the intersection of their domains and $\kappa_{1}$ and $\kappa_{2}$ coincide; and (ii) $F_{0} \leqslant F_{1} \leqslant F_{2}$ implies $\operatorname{dom}\left(F_{0}\right) \cap \operatorname{dom}\left(F_{2}\right) \subseteq \operatorname{dom}\left(F_{1}\right)$. Let $\leqslant^{+}, \leqslant^{-}$, and $\leqslant^{ \pm}$stand for $\leqslant, \geqslant$, and $=$, respectively. Then, define the interpretation of subtyping as follows: if $t_{1}, t_{2} \in \mathcal{M}_{\kappa}$, let $t_{1} \leq t_{2}$ hold if and only if, for every path $\pi \in \operatorname{dom}\left(t_{1}\right) \cap \operatorname{dom}\left(t_{2}\right), t_{1}(\pi) \leqslant^{\nu(\pi)} t_{2}(\pi)$ holds. It is not difficult to check that $\leq$ is a partial order on every $\mathcal{M}_{\kappa}$. The reader is referred to (Kozen, Palsberg, and Schwartzbach., 1995) for more details about this construction. Models that define subtyping in this manner are referred to as nonstructural subtyping models.

A simple nonstructural subtyping model is obtained by letting the directions domain and codomain be contra- and covariant, respectively, and introducing, in addition to the type constructor $\rightarrow$, two type constructors $\perp$ and $T$ of signature $\star$. This gives rise to a model where $\perp$ is the least ground type, $T$ is the greatest ground type, and the arrow type constructor is, as usual, contravariant in its domain and covariant in its codomain.

A typical use of nonstructural subtyping is in type systems for records. One may, for instance, introduce a covariant direction content of kind $\star$, a kind $\diamond$, a type constructor abs of signature $\diamond$, a type constructor pre of signature $\{$ content $\mapsto \star\} \Rightarrow \diamond$, and let pre $\leqslant$ abs. This gives rise to a model where pre $t \leq$ abs holds for every $t \in \mathcal{M}_{\star}$. This form of subtyping is called nonstructural because comparable ground types may have different shapes, such as $\perp$ and $\perp \rightarrow \top$, or pre $T$ and abs. Nonstructural subtyping has been studied, for example, in (Kozen, Palsberg, and Schwartzbach., 1995; Palsberg, Wand, and O'Keefe, 1997; Pottier, 2001b; Niehren and Priesnitz, 2003). Section 1.11 says more about typechecking operations on records.

An important particular case arises when any two type constructors related by $\leqslant$ have the same arity. In that case, it is not difficult to show that any two ground types related by subtyping must have the same shape, that is, if $t_{1} \leq t_{2}$ holds, then $\operatorname{dom}\left(t_{1}\right)$ and $\operatorname{dom}\left(t_{2}\right)$ coincide. For this reason, such an interpretation of subtyping is usually referred to as atomic or structural subtyping. It has been studied in the finite (Mitchell, 1984, 1991b; Frey, 1997; Rehof, 1997; Kuncak and Rinard, 2003; Simonet, 2003) and regular (Tiuryn and Wand,

1993) cases. Structural subtyping is often used in automated program analyses that enrich standard types with atomic annotations without altering their shape.

Our last example suggests a predicate other than equality and subtyping.

1.3.10 Example [Conditional Constraints]: Consider a nonstructural subtyping model. For every type constructor $F$ of image kind $\kappa$ and for every kind $\kappa^{\prime}$, let $(F \leqslant \cdot \Rightarrow \cdot \leq \cdot)$ be a predicate of signature $\kappa \otimes \kappa^{\prime} \otimes \kappa^{\prime} \Rightarrow \cdot$. Thus, if $\mathrm{T}_{0}$ has kind $\kappa$ and $\mathrm{T}_{1}, \mathrm{~T}_{2}$ have the same kind, then $F \leqslant \mathrm{~T}_{0} \Rightarrow \mathrm{T}_{1} \leq \mathrm{T}_{2}$ is a wellformed constraint, called a conditional subtyping constraint. Its interpretation is defined as follows: if $t_{0} \in \mathcal{M}_{\kappa}$ and $t_{1}, t_{2} \in \mathcal{M}_{\kappa^{\prime}}$, then $F \leqslant t_{0} \Rightarrow t_{1} \leq t_{2}$ holds if and only if $F \leqslant t_{0}(\epsilon)$ implies $t_{1} \leq t_{2}$. In other words, if $t_{0}$ 's head symbol exceeds $F$ according to the ordering on type constructors, then the subtyping constraint $t_{1} \leq t_{2}$ must hold; otherwise, the conditional constraint holds vacuously. Conditional constraints have been studied e.g. in (Reynolds, 1969a; Heintze, 1993; Aiken, Wimmers, and Lakshman, 1994; Pottier, 2000; Su and Aiken, 2001).

Many other kinds of constraints exist; see e.g. (Comon, 1993).

Throughout this chapter, we assume (unless stated otherwise) that the set of type constructors, the set of predicates, and the model-which, together, form the parameter $X$-are arbitrary and fixed.

As usual, the meaning of a constraint is a function of the meaning of its free type variables, which is given by a ground assignment. The meaning of free program identifiers may be defined as part of the constraint, if desired, using a def prefix, so it need not be given by a separate assignment.

1.3.11 Definition: A ground assignment $\phi$ is a total, kind-preserving mapping from $\mathcal{V}$ into $\mathcal{M}$. Ground assignments are extended to types by $\phi\left(F \mathrm{~T}_{1} \ldots \mathrm{T}_{n}\right)=$ $F\left(\phi\left(\mathrm{T}_{1}\right), \ldots, \phi\left(\mathrm{T}_{n}\right)\right)$. Then, for every type $\mathrm{T}$ of kind $\kappa, \phi(\mathrm{T})$ is a ground type of kind $\kappa$. Whether a constraint $C$ holds under a ground assignment $\phi$, written $\phi \vdash C$ (read: $\phi$ satisfies $C$ ), is defined by the rules in Figure 1-5. A constraint $C$ is satisfiable if and only if $\phi \vdash C$ holds for some $\phi$. It is false if and only if $\phi \vdash \operatorname{def} \Gamma$ in $C$ holds for no ground assignment $\phi$ and environment $\Gamma$.

Let us now explain the rules that define constraint satisfaction (Figure 15). They are syntax-directed: that is, to a given constraint, at most one rule applies. It is determined by the nature of the first construct that appears under a maximal def prefix. CM-TRUE states that a constraint of the form def $\Gamma$ in true is a tautology, that is, holds under every ground assignment. No rule matches constraints of the form def $\Gamma$ in false, which means that such constraints do not have a solution. CM-PREDICATE states that the meaning

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-027.jpg?height=396&width=1502&top_left_y=228&top_left_x=239)

Figure 1-5: Meaning of constraints

of a predicate application is given by the predicate's interpretation within the model. More specifically, if $P$ 's signature is $\kappa_{1} \otimes \ldots \otimes \kappa_{n} \Rightarrow \cdot$, then, by wellformedness of the constraint, every $\mathrm{T}_{i}$ is of kind $\kappa_{i}$, so $\phi\left(\mathrm{T}_{i}\right)$ is a ground type in $\mathcal{M}_{\kappa_{i}}$. By Definition 1.3.5, $P$ denotes a predicate on $\mathcal{M}_{\kappa_{1}} \times \ldots \times \mathcal{M}_{\kappa_{n}}$, so the rule's premise is mathematically well-formed. It is independent of $\Gamma$, which is natural, since a predicate application has no free program identifiers. CMAND requires each of the conjuncts to be valid in isolation. The information in $\Gamma$ is made available to each branch. CM-ExisTs allows the type variables $\overrightarrow{\mathrm{X}}$ to denote arbitrary ground types $\vec{t}$ within $C$, independently of their image through $\phi$. We implicitly require $\overrightarrow{\mathrm{X}}$ and $\vec{t}$ to have matching kinds, so that $\phi[\overrightarrow{\mathrm{X}} \mapsto \vec{t}]$ remains a kind-preserving ground assignment. The side condition $\overline{\mathrm{x}} \# \mathrm{ftv}(\Gamma)$ - which may always be satisfied by suitable $\alpha$-conversion of the constraint $\exists \overline{\mathrm{X}} . C$ - prevents free occurrences of the type variables $\overline{\mathrm{X}}$ within $\Gamma$ from being unduly affected. CM-INSTANCE concerns constraints of the form def $\Gamma$ in $\mathrm{x} \preceq \mathrm{T}^{\prime}$. The constraint $\mathrm{x} \preceq \mathrm{T}^{\prime}$ is turned into $\sigma \preceq \mathrm{T}^{\prime}$, where, according to the second premise, $\sigma$ is $\Gamma(\mathrm{x})$. Please recall that constraints of such a form were introduced in Definition 1.3.3. The environment $\Gamma$ is replaced with a suitable prefix of itself, namely $\Gamma_{1}$, so that the free program identifiers of $\sigma$ retain their meaning.

It is intuitively clear that the constraints def $\mathrm{x}: \sigma$ in $C$ and $[\mathrm{x} \mapsto \sigma] C$ have the same meaning, where the latter denotes the capture-avoiding substitution of $\sigma$ for x throughout $C$. As a matter of fact, it would have been possible to use this equivalence as a definition of the meaning of def constraints, but the present style is pleasant as well. This confirms our (informal) claim that the def form is an explicit substitution form.

It is possible for a constraint to be neither satisfiable nor false. Consider, for instance, the constraint $\exists \mathrm{Z} \cdot \mathrm{x} \preceq \mathrm{z}$. Because the identifier $\mathrm{x}$ is free, CMINSTANCE is not applicable, so the constraint is not satisfiable. Furthermore,
placing it within the context let $\mathrm{x}: \forall \mathrm{X} . \mathrm{X}$ in $\square$ makes it satisfied by every ground assignment, so it is not false. Here, the assertions " $C$ is satisfiable" and " $C$ is false" are opposite when $f p i(C)=\varnothing$ holds, whereas in a standard first-order logic, they always are.

In a judgement of the form $\phi \vdash C$, the ground assignment $\phi$ applies to the free type variables of $C$. This is made precise by the following statements. In the second one, $\circ$ is composition and $\theta(C)$ is the capture-avoiding application of the type substitution $\theta$ to $C$.

1.3.12 Lemma: If $\overline{\mathrm{x}} \# \operatorname{ftv}(C)$ holds, then $\phi \vdash C$ and $\phi[\overrightarrow{\mathrm{x}} \mapsto \vec{t}] \vdash C$ are equivalent.

1.3.13 Lemma: $\phi \circ \theta \vdash C$ and $\phi \vdash \theta(C)$ are equivalent.

\section*{Reasoning with constraints}

Because constraints lie at the heart of our treatment of ML-the-type-system, most of our proofs involve establishing logical properties of constraints, that is, entailment or equivalence assertions. Let us first define these notions.

1.3.14 Definition: We write $C_{1} \Vdash C_{2}$, and say that $C_{1}$ entails $C_{2}$, if and only if, for every ground assignment $\phi$ and for every environment $\Gamma, \phi \vdash \operatorname{def} \Gamma$ in $C_{1}$ implies $\phi \vdash \operatorname{def} \Gamma$ in $C_{2}$. We write $C_{1} \equiv C_{2}$, and say that $C_{1}$ and $C_{2}$ are equivalent, if and only if $C_{1} \Vdash C_{2}$ and $C_{2} \Vdash C_{1}$ hold.

This definition measures the strength of a constraint by the set of pairs $(\phi, \Gamma)$ that satisfy it, and considers a constraint stronger if fewer such pairs satisfy it. In other words, $C_{1}$ entails $C_{2}$ when $C_{1}$ imposes stricter requirements on its free type variables and program identifiers than $C_{2}$ does. We remark that $C$ is false if and only if $C \equiv$ false holds. It is straightforward to check that entailment is reflexive and transitive and that $\equiv$ is indeed an equivalence relation.

We immediately exploit the notion of constraint equivalence to define what it means for a type constructor to be covariant, contravariant, or invariant with respect to one of its parameters. Let $F$ be a type constructor of signature $\kappa_{1} \otimes$ $\ldots \otimes \kappa_{n} \Rightarrow \kappa$. Let $i \in\{1, \ldots, n\} . F$ is covariant (resp. contravariant, invariant) with respect to its $i^{\text {th }}$ parameter if and only if, for all types $\mathrm{T}_{1}, \ldots, \mathrm{T}_{n}$ and $\mathrm{T}_{i}^{\prime}$ of appropriate kinds, the constraint $F \mathrm{~T}_{1} \ldots \mathrm{T}_{i} \ldots \mathrm{T}_{n} \leq F \mathrm{~T}_{1} \ldots \mathrm{T}_{i}^{\prime} \ldots \mathrm{T}_{n}$ is equivalent to $\mathrm{T}_{i} \leq \mathrm{T}_{i}^{\prime}$ (resp. $\mathrm{T}_{i}^{\prime} \leq \mathrm{T}_{i}, \mathrm{~T}_{i}=\mathrm{T}_{i}^{\prime}$ ). We let the reader check the following facts: (i) in an equality model, these three notions coincide; (ii) in an equality free tree model, every type constructor is invariant with respect to each of its parameters; and (iii) in a nonstructural subtyping model, if the direction $d$ has been declared covariant (resp. contravariant, invariant), then every type constructor whose arity includes $d$ is covariant (resp. contravariant,
invariant) with respect to $d$. In the following, we require the type constructor $\rightarrow$ to be contravariant with respect to its domain and covariant with respect to its codomain - a standard requirement in type systems with subtyping (TAPL Chapter 15). These properties are summed up by the following equivalence law:

$$
\begin{equation*}
\mathrm{T}_{1} \rightarrow \mathrm{T}_{2} \leq \mathrm{T}_{1}^{\prime} \rightarrow \mathrm{T}_{2}^{\prime} \equiv \mathrm{T}_{1}^{\prime} \leq \mathrm{T}_{1} \wedge \mathrm{T}_{2} \leq \mathrm{T}_{2}^{\prime} \tag{C-ARrow}
\end{equation*}
$$

Please note that this is a high-level requirement about the interpretation of types and of the subtyping predicate. In an equality free tree model, for instance, it is always satisfied. In a nonstructural subtyping model, it boils down to requiring that the directions domain and codomain be declared contravariant and covariant, respectively. In the general case, we do not have any knowledge of the model, and cannot formulate a more precise requirement. Thus, it is up to the designer of the model to ensure that C-ARrow holds.

We also exploit the notion of constraint equivalence to define what it means for two type constructors to be incompatible. Two type constructors $F_{1}$ and $F_{2}$ with the same image kind are incompatible if and only if all constraints of the form $F_{1} \overrightarrow{\mathrm{T}}_{1} \leq F_{2} \overrightarrow{\mathrm{T}}_{2}$ and $F_{2} \overrightarrow{\mathrm{T}}_{2} \leq F_{1} \overrightarrow{\mathrm{T}}_{1}$ are false; then, we write $F_{1} \bowtie F_{2}$. Please note that in an equality free tree model, any two distinct type constructors are incompatible. In the following, we often indicate that a newly introduced type constructor must be isolated. We implicitly require that, whenever each of $F_{1}$ and $F_{2}$ is isolated, $F_{1}$ and $F_{2}$ be incompatible. Thus, the notion of "isolation" provides a concise and modular way of stating a collection of incompatibility requirements. We consider the type constructor $\rightarrow$ isolated.

Entailment is preserved by arbitrary constraint contexts, as stated by the following theorem. As a result, constraint equivalence is a congruence. Throughout this chapter, these facts are often used implicitly.

1.3.15 Theorem [Congruence]: $C_{1} \Vdash C_{2}$ implies $\mathcal{C}\left[C_{1}\right] \Vdash \mathcal{C}\left[C_{2}\right]$.

We now give a series of lemmas that provide useful entailment laws.

The following is a standard property of existential quantification.

1.3.16 Lemma: $C \Vdash \exists \overline{\mathrm{x}}$. $C$.

The following lemma states that any supertype of an instance of $\sigma$ is also an instance of $\sigma$.

1.3.17 Lemma: $\sigma \preceq \mathrm{T} \wedge \mathrm{T} \leq \mathrm{T}^{\prime} \Vdash \sigma \preceq \mathrm{T}^{\prime}$.

The next lemma gives another interesting simplification law.

1.3.18 Lemma: $\mathrm{X} \notin f t v(\mathrm{~T})$ implies $\exists \mathrm{X} .(\mathrm{X}=\mathrm{T}) \equiv$ true.

The following lemma states that, provided $D$ is satisfied, the type $\mathrm{T}$ is an instance of the constrained type scheme $\forall \overline{\mathrm{x}}[D]$.T.

1.3.19 Lemma: $D \Vdash \forall \overline{\mathrm{X}}[D] . \mathrm{T} \preceq \mathrm{T}$.

This technical lemma helps justify Definition 1.3.21 below.

1.3.20 Lemma: Let $\mathrm{Z} \notin \operatorname{ftv}(C, \sigma, \mathrm{T})$. Then, $C \Vdash \sigma \preceq \mathrm{T}$ holds if and only if $C \wedge \mathrm{T} \leq$ $\mathrm{Z} \Vdash \sigma \preceq \mathrm{Z}$ holds.

It is useful to define what it means for a type scheme $\sigma_{1}$ to be more general than a type scheme $\sigma_{2}$. Our informal intent is for $\sigma_{1} \preceq \sigma_{2}$ to mean: every instance of $\sigma_{2}$ is an instance of $\sigma_{1}$. In Definition 1.3.3, we have introduced the constraint form $\sigma \preceq \mathrm{T}$ as syntactic sugar. Similarly, one might wish to make $\sigma_{1} \preceq \sigma_{2}$ a derived constraint form; however, this is impossible, because neither universal quantification nor implication are available in the constraint language. We can, however, exploit the fact that these logical connectives are implicit in entailment assertions by defining a judgement of the form $C \Vdash \sigma_{1} \preceq \sigma_{2}$, whose meaning is: under the constraint $C$, $\sigma_{1}$ is more general than $\sigma_{2}$.

1.3.21 Definition: We write $C \Vdash \sigma_{1} \preceq \sigma_{2}$ if and only if $\mathrm{Z} \notin \operatorname{ftv}\left(C, \sigma_{1}, \sigma_{2}\right)$ implies $C \wedge \sigma_{2} \preceq \mathrm{Z} \Vdash \sigma_{1} \preceq \mathrm{z}$. We write $C \Vdash \sigma_{1} \equiv \sigma_{2}$ when both $C \Vdash \sigma_{1} \preceq \sigma_{2}$ and $C \Vdash \sigma_{2} \preceq \sigma_{1}$ hold.

This notation is not ambiguous because the assertion $C \Vdash \sigma \preceq \mathrm{T}$, whose meaning was initially given by Definitions 1.3 .3 and 1.3.14, retains the same meaning under the new definition - this is shown by Lemma 1.3.20 above.

The next lemma provides a way of exploiting the ordering between type schemes introduced by Definition 1.3.21. It states that a type scheme occurs in contravariant position when it is within a def prefix. In other words, the more general the type scheme, the weaker the entire constraint.

1.3.22 Lemma: $C \Vdash \sigma_{1} \preceq \sigma_{2}$ implies $C \wedge \operatorname{def} \mathrm{x}: \sigma_{2}$ in $D \Vdash \operatorname{def} \mathrm{x}: \sigma_{1}$ in $D$.

The following exercise generalizes this result to let forms.

1.3.23 EXERcISE $[\star \star, \nrightarrow]$ : Prove that $\mathrm{Z} \notin f t v(\sigma)$ implies $\exists \sigma \equiv \exists \mathrm{Z} . \sigma \preceq \mathrm{Z}$. Explain why, as a result, $C \Vdash \sigma_{1} \preceq \sigma_{2}$ implies $C \wedge \exists \sigma_{2} \Vdash \exists \sigma_{1}$. Use this fact to prove that $C \Vdash \sigma_{1} \preceq \sigma_{2}$ implies $C \wedge$ let x : $\sigma_{2}$ in $D \Vdash$ let $\mathrm{x}: \sigma_{1}$ in $D$.

The next lemma states that, modulo equivalence, the only constraint that constrains $\mathrm{x}$ without explicitly referring to it is false.

1.3.24 Lemma: $C \Vdash \mathrm{x} \preceq \mathrm{T}$ and $\mathrm{x} \notin f p i(C)$ imply $C \equiv$ false.

The following lemma states that the more universal quantifiers are present, the more general the type scheme.

1.3.25 Lemma: let $\mathrm{x}: \forall \overline{\mathrm{x}}\left[C_{1}\right] . \mathrm{T}$ in $C_{2} \Vdash$ let $\mathrm{x}: \forall \overline{\mathrm{x}} \overline{\mathrm{Y}}\left[C_{1}\right] . \mathrm{T}$ in $C_{2}$.

Conversely, and perhaps surprisingly, it is sometimes possible to remove some type variables from the universal quantifier prefix of a type scheme without compromising its generality. This is the case when the value of these type variables is determined in a unique way. In short, $C$ determines $\overline{\mathrm{Y}}$ if and only if, given the values of $f t v(C) \backslash \overline{\mathrm{Y}}$ and given that $C$ holds, it is possible to reconstruct, in a unique way, the values of $\bar{Y}$.

1.3.26 Definition: $C$ determines $\overline{\mathrm{Y}}$ if and only if, for every environment $\Gamma$, two ground assignments that satisfy def $\Gamma$ in $C$ and that coincide outside $\bar{Y}$ must coincide on $\bar{Y}$ as well.

Two concrete instances of determinacy, one of which is valid only in free tree models, are given by Lemma 1.8.7 on page 82. Determinacy is exploited by the equivalence law C-LETALL in Figure 1-6.

We now give a toolbox of constraint equivalence laws. It is worth noting that they do not form a complete axiomatization of constraint equivalencein fact, they cannot, since the syntax and meaning of constraints is partly unspecified.

1.3.27 Theorem: All equivalence laws in Figure 1-6 hold.

Let us explain. C-AND and C-ANDAnd state that conjunction is commutative and associative. C-DuP states that redundant conjuncts may be freely added or removed, where a conjunct is redundant if and only if it is entailed by another conjunct. Throughout this chapter, these three laws are often used implicitly. C-ExEx and C-Ex* allow grouping consecutive existential quantifiers and suppressing redundant ones, where a quantifier is redundant if and only if it does not occur free within its scope. C-ExAnd allows conjunction and existential quantification to commute, provided no capture occurs; it is known as a scope extrusion law. When the rule is oriented from left to right, its side-condition may always be satisfied by suitable $\alpha$-conversion. C-ExTrans states that it is equivalent for a type $\mathrm{T}^{\prime}$ to be an instance of $\sigma$ or to be a supertype of some instance of $\sigma$. We remark that the instances of a monotype are its supertypes, that is, by Definition 1.3.3, $\mathrm{T} \preceq \mathrm{T}^{\prime}$ and $\mathrm{T} \leq \mathrm{T}^{\prime}$ are equivalent. As a result, specializing C-ExTRans to the case where $\sigma$ is a monotype, we find that $\mathrm{T} \leq \mathrm{T}^{\prime}$ is equivalent to $\exists \mathrm{Z}$. $\left(\mathrm{T} \leq \mathrm{Z} \wedge \mathrm{Z} \leq \mathrm{T}^{\prime}\right.$ ), for fresh $\mathrm{Z}$, a standard equivalence law. When oriented from left to right, it becomes an interesting simplification law: in a chain of subtyping constraints, an intermediate variable such as Z may be suppressed, provided it is local, as witnessed by the existential quantifier $\exists \mathrm{Z}$. C-INID states that, within the scope of the binding $\mathrm{x}: \sigma$, every free occurrence of $\mathrm{x}$ may be safely replaced with $\sigma$. The restriction to free occurrences stems from the side-condition $\mathrm{x} \notin d p i(\mathcal{C})$. When the

$$
\begin{aligned}
& C_{1} \wedge C_{2} \equiv C_{2} \wedge C_{1} \\
& \left(C_{1} \wedge C_{2}\right) \wedge C_{3} \equiv C_{1} \wedge\left(C_{2} \wedge C_{3}\right) \\
& C_{1} \wedge C_{2} \equiv C_{1} \quad \text { if } C_{1} \Vdash C_{2} \\
& \exists \overline{\mathrm{X}} \cdot \exists \overline{\mathrm{Y}} \cdot C \equiv \exists \overline{\mathrm{X}} \overline{\mathrm{Y}} \cdot C \\
& \exists \overline{\mathrm{x}} . C \equiv C \\
& \left(\exists \overline{\mathrm{X}} \cdot C_{1}\right) \wedge C_{2} \equiv \exists \overline{\mathrm{X}} \cdot\left(C_{1} \wedge C_{2}\right) \\
& \text { (C-DuP) } \\
& (\mathrm{C}-\mathrm{ExEx}) \\
& \left(\mathrm{C}-\mathrm{Ex}^{*}\right) \\
& \exists \mathrm{Z} .\left(\sigma \preceq \mathrm{Z} \wedge \mathrm{Z} \leq \mathrm{T}^{\prime}\right) \equiv \sigma \preceq \mathrm{T}^{\prime} \\
& \text { if } \overline{\mathrm{x}} \# \mathrm{ftv}(C) \\
& \text { if } \overline{\mathrm{x}} \# \mathrm{ftv}\left(C_{2}\right) \\
& \text { (C-ExAnd) } \\
& \text { let } \mathrm{x}: \sigma \text { in } \mathcal{C}\left[\mathrm{x} \preceq \mathrm{T}^{\prime}\right] \equiv \text { let } \mathrm{x}: \sigma \text { in } \mathcal{C}\left[\sigma \preceq \mathrm{T}^{\prime}\right] \\
& \text { if } \mathrm{x} \notin d p i(\mathcal{C}) \text { and } \operatorname{dtv}(\mathcal{C}) \# f \operatorname{tv}(\sigma) \text { and }\{\mathrm{x}\} \cup d p i(\mathcal{C}) \# f p i(\sigma) \\
& \text { let } \Gamma \text { in } C \equiv \exists \Gamma \wedge C \quad \text { if } d p i(\Gamma) \# f p i(C) \\
& \text { (C-ExTrans) } \\
& \text { if } \mathbf{z} \notin f t v\left(\sigma, \mathrm{T}^{\prime}\right) \\
& \text { let } \Gamma ; \mathrm{x}: \forall \overline{\mathrm{x}}\left[C_{1}\right] . \mathrm{T} \text { in } C_{2} \equiv \text { let } \Gamma ; \mathrm{x}: \forall \overline{\mathrm{x}}\left[\text { let } \Gamma \text { in } C_{1}\right] . \mathrm{T} \text { in } C_{2} \\
& \text { if } \overline{\mathrm{X}} \# f t v(\Gamma) \text { and } d p i(\Gamma) \# f p i(\Gamma) \\
& \text { if } \overline{\mathrm{Y}} \# \operatorname{ftv}(\mathrm{T}) \\
& \text { true } \equiv \exists \overline{\mathrm{X}} \cdot(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})
\end{aligned}
$$

Figure 1-6: Constraint equivalence laws
rule is oriented from left to right, its other side-conditions, which require the context let $\mathrm{x}: \sigma$ in $\mathcal{C}$ not to capture $\sigma$ 's free type variables or free program identifiers, may always be satisfied by suitable $\alpha$-conversion. C-IN* complements the previous rule by allowing redundant let bindings to be simplified. We remark that C-INID and C-IN* provide a simple procedure for eliminating let forms. C-INAND states that the let form commutes with conjunction; CINAND* spells out a common particular case. C-INEX states that it commutes with existential quantification. When the rule is oriented from left to right, its side-condition may always be satisfied by suitable $\alpha$-conversion. C-LETLET states that let forms may commute, provided they bind distinct program identifiers and provided no free program identifiers are captured in the process. C-LETAnd allows the conjunct $C_{1}$ to be moved outside of the constrained type scheme $\forall \overline{\mathrm{x}}\left[C_{1} \wedge C_{2}\right]$.T, provided it does not involve any of the universally quantified type variables $\overline{\mathrm{X}}$. When oriented from left to right, the rule yields an important simplification law: indeed, taking an instance of $\forall \overline{\mathrm{X}}\left[C_{2}\right]$. T is less expensive than taking an instance of $\forall \overline{\mathrm{x}}\left[C_{1} \wedge C_{2}\right]$. T, since the latter involves creating a copy of $C_{1}$, while the former does not. C-LETDUP allows pushing a series of let bindings into a constrained type scheme, provided no capture occurs in the process. It is not used as a simplification law but as a tool in some proofs. C-LETEx states that it does not make any difference for a set of type variables $\bar{Y}$ to be existentially quantified inside a constrained type scheme or part of the type scheme's universal quantifiers. Indeed, in either case, taking an instance of the type scheme means producing a constraint where $\bar{Y}$ is existentially quantified. C-LETALL provides a restricted converse of Lemma 1.3.25. Together, C-LETEx and C-LETALL allow-in some situations only - to hoist existential quantifiers out of the left-hand side of a let form.

1.3.28 Example: C-LetAll would be invalid without the condition that $\exists \overline{\mathrm{X}} . C_{1}$ determines $\bar{Y}$. Consider, for instance, the constraint let $\mathrm{x}: \forall \mathrm{Y} . \mathrm{Y} \rightarrow \mathrm{Y}$ in $(\mathrm{x} \preceq$ int $\rightarrow$ int $\wedge \mathrm{x} \preceq$ bool $\rightarrow$ bool) (1), where int and bool are incompatible nullary type constructors. By C-INID and C-IN*, it is equivalent to $\exists \mathrm{Y}$. $\mathrm{Y} \rightarrow$ $\mathrm{Y} \leq$ int $\rightarrow$ int $) \wedge \exists \mathrm{Y}$. $\mathrm{Y} \rightarrow \mathrm{Y} \leq$ bool $\rightarrow$ bool $)$, that is, true. Now, if C-LETALL was valid without its side-condition, then (1) would also be equivalent to $\exists \mathrm{Y}$.let $\mathrm{x}: \mathrm{Y} \rightarrow \mathrm{Y}$ in $(\mathrm{x} \preceq$ int $\rightarrow$ int $\wedge \mathrm{x} \preceq$ bool $\rightarrow$ bool), which by C-INID and C-IN* is $\exists \mathrm{Y}$.(Y $\rightarrow \mathrm{Y} \leq$ int $\rightarrow$ int $\wedge \mathrm{Y} \rightarrow \mathrm{Y} \leq$ bool $\rightarrow$ bool). By C-ARROW and C-ExTrans, this is int $=$ bool, that is, false. Thus, the law is invalid in this case. It is easy to see why: when the type scheme $\sigma$ contains a $\forall \mathrm{Y}$ quantifier, every instance of $\sigma$ receives its own $\exists \mathrm{Y}$ quantifier, making Y a distinct (local) type variable; when $\mathrm{Y}$ is not universally quantified, however, all instances of $\sigma$ share references to a single (global) type variable Y. This corresponds to the
intuition that, in the former case, $\sigma$ is polymorphic in Y, while in the latter case, it is monomorphic in Y. Lemma 1.3.25 states that, when deprived of its sidecondition, C-LETALL is only an entailment law, as opposed to an equivalence law. Similarly, it is in general invalid to hoist an existential quantifier out of the left-hand side of a let form. To see this, one may study the (equivalent) constraint let $\mathrm{x}: \forall \mathrm{X}[\exists \mathrm{Y} . \mathrm{X}=\mathrm{Y} \rightarrow \mathrm{Y}] . \mathrm{X}$ in $(\mathrm{x} \preceq$ int $\rightarrow$ int $\wedge \mathrm{x} \preceq$ bool $\rightarrow$ bool).

Naturally, in the above examples, the side-condition "true determines $\mathrm{Y}$ " does not hold: by Definition 1.3.26, it is equivalent to "two ground assignments that coincide outside Y must coincide on Y as well', which is false as soon as $\mathcal{M}_{\star}$ contains two distinct elements, such as int and bool here. There are cases, however, where the side-condition does hold. For instance, we later prove that $\exists X . Y=$ int determines $Y$; see Lemma 1.8.7. As a result, C-LETALL states that let $\mathrm{x}: \forall \mathrm{XY}[\mathrm{Y}=$ int]. $\mathrm{Y} \rightarrow \mathrm{X}$ in $C$ (1) is equivalent to $\exists \mathrm{Y}$.let $\mathrm{x}: \forall \mathrm{X}[\mathrm{Y}=\operatorname{int}] . \mathrm{Y} \rightarrow$ $\mathrm{X}$ in $C$ (2), provided $\mathrm{Y} \notin f t v(C)$. The intuition is simple: because $\mathrm{Y}$ is forced to assume the value int by the equation $\mathrm{Y}=$ int, it makes no difference whether $Y$ is or isn't universally quantified. We remark that, by C-LETAND, (2) is equivalent to $\exists \mathrm{Y}$. $\mathrm{Y}=\operatorname{int} \wedge$ let $\mathrm{x}: \forall \mathrm{X} . \mathrm{Y} \rightarrow \mathrm{X}$ in $C$ ) (3). In an efficient constraint solver, simplifying (1) into (3) before using C-INID to eliminate the let form is worthwhile, since doing so obviates the need for copying the type variable $\mathrm{Y}$ and the equation $\mathrm{Y}=$ int at every free occurrence of $\mathrm{x}$ inside $C$.

C-LETSuB is the analogue of an environment strengthening lemma: roughly speaking, it states that, if a constraint holds under the assumption that $\mathrm{x}$ has type $\mathrm{X}$, where $\mathrm{X}$ is some supertype of $\mathrm{T}$, then it also holds under the assumption that $\mathrm{x}$ has type $\mathrm{T}$. The last three rules deal with the equality predicate. $\mathrm{C}-\mathrm{EQ}$ states that it is valid to replace equals with equals; note the absence of a side-condition. When oriented from left to right, C-NAME allows introducing fresh names $\overrightarrow{\mathrm{X}}$ for the types $\overrightarrow{\mathrm{T}}$. As always, $\overrightarrow{\mathrm{X}}$ stands for a vector of distinct type variables. Of course, this makes sense only if the definition is not circular, that is, if the type variables $\overline{\mathrm{X}}$ do not occur free within the terms $\overline{\mathrm{T}}$. When oriented from right to left, C-NAME may be viewed as a simplification law: it allows eliminating type variables whose value has been determined. C-NAMEEQ is a combination of $\mathrm{C}-\mathrm{EQ}$ and $\mathrm{C}-\mathrm{NAME}$. It shows that applying an idempotent substitution to a constraint $C$ amounts to placing $C$ within a certain context. This immediately yields a proof of the following fact:

1.3.29 Lemma: $C \Vdash D$ implies $\theta(C) \Vdash \theta(D)$.

It is important to stress that, because the effect of a type substitution may be emulated using equations, conjunction, and existential quantification, there is no need ever to employ type substitutions in the definition of a constraintbased type system - it is possible, instead, to express every concept in terms
of constraints. In this chapter, we follow this route, and use type substitutions only when dealing with the type system DM, whose historical formulation is substitution-based.

So far, we have considered def a primitive constraint form and defined the let form in terms of def, conjunction, and existential quantification. The motivation for this approach was to simplify the proof of several constraint equivalence laws. However, in the remainder of this chapter, we work with let forms exclusively and never employ the def construct. As a result, it is possible, from here on, to discard def and pretend that let is primitive. This change in perspective offers us a few extra properties, stated in the next two lemmas. First, every constraint that contains a false subconstraint must be false. Second, no satisfiable constraint has a free program identifier.

1.3.30 Lemma: $\mathcal{C}[$ false $] \equiv$ false.

1.3.31 Lemma: If $C$ is satisfiable, then $f p i(C)=\varnothing$.

\section*{Reasoning with constraints in an equality-only syntactic model}

We have given a number of equivalence laws that are valid with respect to any interpretation of constraints, that is, within any model. However, an important special case is that of equality-only syntactic models. Indeed, in that specific setting, our constraint-based type systems are in close correspondence with DM. In short, we aim to prove that every satisfiable constraint admits a canonical solved form, to show that this notion corresponds to the standard concept of a most general unifier, and to establish a few technical properties of most general unifiers.

Thus, let us now assume that constraints are interpreted in an equality-only syntactic model. Let us further assume that, for every kind $\kappa$, (i) there are at least two type constructors of image kind $\kappa$ and (ii) for every type constructor $F$ of image kind $\kappa$, there exists $t \in \mathcal{M}_{\kappa}$ such that $t(\epsilon)=F$. We refer to models that violate (i) or (ii) as degenerate; one may argue that such models are of little interest. The assumption that the model is nondegenerate is used in the proof of Lemmas 1.3.32 and 1.3.39.

Under these new assumptions, the interpretation of equality coincides with its syntax: every equation that holds in the model is in fact a syntactic truism. The converse, of course, holds in every model.

1.3.32 Lemma: If true $\Vdash \mathrm{T}=\mathrm{T}^{\prime}$ holds, then $\mathrm{T}$ and $\mathrm{T}^{\prime}$ coincide.

In a syntactic model, ground types are finite trees. As a result, cyclic equations, such as $\mathrm{X}=$ int $\rightarrow \mathrm{X}$, are false.

1.3.33 Lemma: $\mathrm{X} \in f t v(\mathrm{~T})$ and $\mathrm{T} \notin \mathcal{V}$ imply $(\mathrm{X}=\mathrm{T}) \equiv$ false.

A solved form is a conjunction of equations, where the left-hand sides are distinct type variables that do not appear in the right-hand sides, possibly surrounded by a number of existential quantifiers. Our definition is identical to Lassez, Maher and Marriott's solved forms (1988) and to Jouannaud and Kirchner's tree solved forms (1991), except we allow for prenex existential quantifiers, which are made necessary by our richer constraint language. Jouannaud and Kirchner also define $d a g$ solved forms, which may be exponentially smaller. Because we define solved forms only for proof purposes, we need not take performance into account at this point. The efficient constraint solver presented in Section 1.8 does manipulate graphs, rather than trees. Type scheme introduction and instantiation constructs cannot appear within solved forms; indeed, provided the constraint at hand has no free program identifiers, they can be expanded away. For this reason, their presence in the constraint language has no impact on the results contained in this section.

1.3 .34 Definition: A solved form is of the form $\exists \overline{\mathrm{Y}} .(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$, where $\overline{\mathrm{X}} \# \mathrm{ftv}(\overline{\mathrm{T}})$.

Solved forms offer a convenient way of reasoning about constraints because every satisfiable constraint is equivalent to one. In other words, every constraint is equivalent to either a solved form or false. This property is established by the following lemma, whose proof provides a simple but effective procedure to rewrite a constraint to either a solved form or false.

1.3.35 Lemma: Let $f p i(C)=\varnothing$. Then, $C$ is equivalent to either a solved form or false.

Proof: We first establish that every conjunction of equations is equivalent to either a solved form or false. To do so, we present Robinson's unification algorithm (1971) as a rewriting system. The system's invariant is to operate on constraints of the form either $\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}} ; C$, where $\overline{\mathrm{X}} \# \operatorname{tv}(\overline{\mathrm{T}}, C)$ and the semicolon is interpreted as a distinguished conjunction, or false. We identify equations in $C$ up to commutativity. The system is defined as follows:

$$
\begin{array}{rrll}
\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}} ; & \mathrm{X}=\mathrm{X} \wedge C \rightarrow & \overrightarrow{\mathrm{x}}=\overrightarrow{\mathrm{T}} ; C \\
\overrightarrow{\mathrm{x}}= & \overrightarrow{\mathrm{T}} ; & F \overrightarrow{\mathrm{T}}_{1}=F \overrightarrow{\mathrm{T}}_{2} \wedge C \rightarrow & \rightarrow \overrightarrow{\mathrm{x}}=\overrightarrow{\mathrm{T}} ; \overrightarrow{\mathrm{T}}_{1}=\overrightarrow{\mathrm{T}}_{2} \wedge C \\
\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}} ; & F_{1} \overrightarrow{\mathrm{T}}_{1}=F_{2} \overrightarrow{\mathrm{T}}_{2} \wedge C \rightarrow & \rightarrow & \text { false } \\
& & & \text { if } F_{1} \neq F_{2} \\
\overrightarrow{\mathrm{X}}= & \overrightarrow{\mathrm{T}} ; & \mathrm{X}=\mathrm{T} \wedge C \rightarrow & \rightarrow \overrightarrow{\mathrm{X}}=[\mathrm{X} \mapsto \mathrm{T}] \overrightarrow{\mathrm{T}} \wedge \mathrm{X}=\mathrm{T} ;[\mathrm{X} \mapsto \mathrm{T}] C \\
& & & \text { if } \mathrm{X} \notin f t v(\mathrm{~T}) \\
\overrightarrow{\mathrm{x}}= & \overrightarrow{\mathrm{T}} ; & \mathrm{X}=\mathrm{T} \wedge C \rightarrow & \text { false } \\
& & & \text { if } \mathrm{X} \in f t v(\mathrm{~T}) \text { and } \mathrm{T} \notin \mathcal{V}
\end{array}
$$

It is straightforward to check that the above invariant is indeed preserved by the rewriting system. Let us check that constraint equivalence is also preserved. For the first rule, this is immediate. For the second and third rules, it
follows from the fact that we have assumed a free tree model; for the fourth rule, a consequence of $\mathrm{C}-\mathrm{EQ}$; for the last rule, a consequence of Lemma 1.3.33. Furthermore, the system is terminating; this is witnessed by an ordering where false is the least element and where constraints of the form $\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}} ; C$ are ordered lexicographically, first by the number of type variables that appear free within $C$, second by the size of $C$. Last, a normal form for this rewriting system must be of the form either $\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}$; true, where (by the invariant) $\overline{\mathrm{X}} \# \mathrm{ftv}(\overline{\mathrm{T}})$ - that is, a solved form, or false.

Next, we show that the present lemma holds when $C$ is built out of equations, conjunction, and existential quantification. Orienting C-ExAnd from left to right yields a terminating rewriting system that preserves constraint equivalence. The normal form of $C$ must be $\exists \overline{\mathrm{Y}}$. $C^{\prime}$, where $C^{\prime}$ is a conjunction of equations. By the previous result, $C^{\prime}$ is equivalent to either a solved form or false. Because solved forms are preserved by existential quantification and because $\exists \bar{Y}$.false is false, the same holds of $C$.

Last, we establish the result in the general case. We assume $f p i(C)=\varnothing$ (1). Orienting C-INID and C-IN* from left to right yields a terminating rewriting system that preserves constraint equivalence. The normal form $C^{\prime}$ of $C$ cannot contain any type scheme introduction forms; given (1), it cannot contain any instantiation forms either. Thus, $C^{\prime}$ is built out of equations, conjunction, and existential quantification only. By the previous result, it is equivalent to either a solved form or false, which implies that the same holds of $C$.

It is possible to impose further restrictions on solved forms. A solved form $\exists \overline{\mathrm{Y}} .(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$ is canonical if and only if its free type variables are exactly $\overline{\mathrm{X}}$. This is stated, in an equivalent way, by the following definition.

1.3.36 Definition: A canonical solved form is a constraint of the form $\exists \overline{\mathrm{Y}}$. $(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$, where $f t v(\overline{\mathrm{T}}) \subseteq \overline{\mathrm{Y}}$ and $\overline{\mathrm{X}} \# \overline{\mathrm{Y}}$.

1.3.37 Lemma: Every solved form is equivalent to a canonical solved form.

It is easy to describe the solutions of a canonical solved form: they are the ground refinements of the substitution $[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}]$.

1.3.38 Lemma: A ground assignment $\phi$ satisfies a canonical solved form $\exists \overline{\mathrm{Y}}$. $(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$ if and only if there exists a ground assignment $\phi^{\prime}$ such that $\phi(\overrightarrow{\mathrm{X}})=\phi^{\prime}(\overrightarrow{\mathrm{T}})$. As a result, every canonical solved form is satisfiable.

Proof: Let $\exists \overline{\mathrm{Y}}$. $(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$ be a canonical solved form. By CM-ExisTs and CMPredicate, $\phi$ satisfies $\exists \overline{\mathrm{Y}}$. $(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$ if and only if there exists $\vec{t}$ such that $\phi[\overrightarrow{\mathrm{Y}} \mapsto$ $\vec{t}](\overrightarrow{\mathrm{X}})=\phi[\overrightarrow{\mathrm{Y}} \mapsto \vec{t}](\overrightarrow{\mathrm{T}})$. Thanks to the hypotheses $\overline{\mathrm{X}} \# \overline{\mathrm{Y}}$ and $f t v(\overline{\mathrm{T}}) \subseteq \overline{\mathrm{Y}}$, this is equivalent to the existence of a ground assignment $\phi^{\prime}$ such that $\phi(\overrightarrow{\vec{X}})=\phi^{\prime}(\overrightarrow{\mathrm{T}})$.

Thus, for every ground assignment $\phi^{\prime}, \phi^{\prime}\left[\overrightarrow{\mathrm{X}} \mapsto \phi^{\prime}(\overrightarrow{\mathrm{T}})\right]$ satisfies $\exists \overline{\mathrm{Y}}$. $(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$, which proves that this constraint is satisfiable.

Together, Lemmas 1.3.37 and 1.3.38 imply that every solved form is satisfiable. Our interest in canonical solved forms stems from the following fundamental property, which provides a syntactic characterization of entailment between canonical solved forms: if $\exists \bar{Y}_{1} \cdot\left(\vec{X}=\vec{T}_{1}\right)$ is more specific than $\exists \bar{Y}_{2} \cdot\left(\vec{X}=\vec{T}_{2}\right)$, in a logical sense, then $\vec{T}_{1}$ refines $\overrightarrow{\mathrm{T}}_{2}$, in a syntactic sense. The converse also holds (can you prove it?), but is not needed here.

1.3.39 LEMma: If $\exists \overline{\mathrm{Y}}_{1} \cdot\left(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}_{1}\right) \Vdash \exists \overline{\mathrm{Y}}_{2} \cdot\left(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}_{2}\right)$, where both sides are canonical solved forms, then there exists a type substitution $\varphi$ such that $\overrightarrow{\mathrm{T}}_{1}=\varphi\left(\overrightarrow{\mathrm{T}}_{2}\right)$.

As a corollary, we find that canonical solved forms are unique up to $\alpha$ conversion and up to $\mathrm{C}$-Ex*, provided the set $\overline{\mathrm{X}}$ of their free type variables is fixed.

1.3.40 LEMma: If the canonical solved forms $\exists \bar{Y}_{1} \cdot\left(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}_{1}\right)$ and $\exists \overline{\mathrm{Y}}_{2} \cdot\left(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}_{2}\right)$ are equivalent, then there exists a renaming $\rho$ such that $\overrightarrow{\mathrm{T}}_{1}=\rho\left(\overrightarrow{\mathrm{T}}_{2}\right)$.

Please note that the fact that the canonical solved forms $\exists \overline{\mathrm{Y}}_{1} \cdot\left(\overrightarrow{\mathrm{X}}_{1}=\overrightarrow{\mathrm{T}}_{1}\right)$ and $\exists \overline{\mathrm{Y}}_{2} \cdot\left(\overrightarrow{\mathrm{X}}_{2}=\overrightarrow{\mathrm{T}}_{2}\right)$ are equivalent does not imply that $\overline{\mathrm{X}}_{1}$ and $\overline{\mathrm{X}}_{2}$ coincide. Consider, for example, the canonical solved forms true and $\exists \mathrm{Y} .(\mathrm{X}=\mathrm{Y})$, which by C-NAMEEQ are equivalent. One might wish to further restrict canonical solved forms by requiring $\overline{\mathrm{X}}$ to be the set of essential type variables of the constraint $\exists \overline{\mathrm{Y}} .(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$, that is, the set of the type variables that appear free in all equivalent constraints. However, as far our technical development is concerned, it seems more convenient not to do so. Instead, we show that it is possible to explicitly restrict or extend $\overline{\mathrm{X}}$ when needed (Lemma 1.3.43).

The following definition allows entertaining a dual view of canonical solved forms, either as constraints or as idempotent type substitutions. The latter view is commonly found in standard treatments of unification (Lassez, Maher, and Marriott, 1988; Jouannaud and Kirchner, 1991) and in classic presentations of ML-the-type-system.

1.3.41 Definition: If $[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}]$ is an idempotent substitution of domain $\overline{\mathrm{X}}$, let $\exists[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}]$ denote the canonical solved form $\exists \overline{\mathrm{Y}} .(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$, where $\overline{\mathrm{Y}}=\operatorname{ftv}(\overline{\mathrm{T}})$. An idempotent substitution $\theta$ is a most general unifier of the constraint $C$ if and only if $\exists \theta$ and $C$ are equivalent.

By definition, equivalent constraints admit the same most general unifiers. Many properties of canonical solved forms may be reformulated in terms of most general unifiers. By Lemmas 1.3.31, 1.3.35, and 1.3.37, every satisfiable constraint admits a most general unifier. By Lemma 1.3.40, if $\left[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}_{1}\right]$ and
$\left[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}_{2}\right]$ are most general unifiers of $C$, then $\overrightarrow{\mathrm{T}}_{1}$ and $\overrightarrow{\mathrm{T}}_{2}$ coincide up to a renaming. Conversely, if $[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}]$ is a most general unifier of $C$ and if $\overline{\mathrm{X}} \# \rho$ holds, then $[\overrightarrow{\mathrm{X}} \mapsto \rho \overrightarrow{\mathrm{T}}]$ is also a most general unifier of $C$; indeed, these two substitutions correspond to $\alpha$-equivalent canonical solved forms.

The following result relates the substitution $\theta$ to the canonical solved form $\exists \theta$, stating that every ground refinement of the former satisfies the latter.

1.3.42 Lemma: $\theta(\exists \theta) \equiv$ true.

The following lemma offers two technical results: the domain of a most general unifier of $C$ may be restricted so as to become a subset of $f t v(C)$; it may also be extended to include arbitrary fresh variables. The next lemma is a simple corollary.

1.3.43 Lemma: Let $\theta$ be a most general unifier of $C$. If $\overline{\mathrm{Z}} \# f \operatorname{tv}(C)$, then $\theta \backslash \overline{\mathrm{z}}$ is also a most general unifier of $C$. If $\overline{\mathrm{z}} \# \theta$, then there exists a most general unifier of $C$ that extends $\theta$ and whose domain is $\operatorname{dom}(\theta) \cup \overline{\mathrm{z}}$.

1.3.44 Lemma: Let $\theta_{1}$ and $\theta_{2}$ be most general unifiers of $C$. Let $\overline{\mathrm{x}}=\operatorname{dom}\left(\theta_{1}\right) \cap$ $\operatorname{dom}\left(\theta_{2}\right)$. Then, $\theta_{1}(\overline{\mathrm{X}})$ and $\theta_{2}(\overline{\mathrm{X}})$ coincide up to a renaming.

Our last technical result relates the most general unifiers of $C$ with the most general unifiers of $\exists$ X.C. It states that the former are extensions of the latter. Furthermore, under a few freshness conditions, every most general unifier of $\exists$ x. $C$ may be extended to yield a most general unifier of $C$.

1.3.45 Lemma: If $\theta$ is a most general unifier of $C$, then $\theta \backslash \mathrm{X}$ is a most general unifier of $\exists \mathrm{x} . C$. Conversely, if $\theta$ is a most general unifier of $\exists \mathrm{X} . C$ and $\mathrm{x} \# \theta$ and $f t v(\exists$ X.C $C) \operatorname{dom}(\theta)$, then there exists a type substitution $\theta^{\prime}$ such that $\theta^{\prime}$ extends $\theta, \theta^{\prime}$ is a most general unifier of $C$, and $\operatorname{dom}\left(\theta^{\prime}\right)=\operatorname{dom}(\theta) \cup \mathrm{X}$.

\section*{$1.4 \operatorname{HM}(X)$}

Constraint-based type systems appeared during the 1980s (Mitchell, 1984; Fuh and Mishra, 1988) and were widely studied during the following decade (Curtis, 1990; Aiken and Wimmers, 1993; Jones, 1994a; Smith, 1994; Palsberg, 1995; Trifonov and Smith, 1996; Fähndrich, 1999; Pottier, 2001b). We now present one such system, baptized $\operatorname{HM}(X)$ because it is a parameterized extension of Hindley and Milner's type discipline; the meaning of the parameter $X$ was explained on page 24. Its original description is due to Odersky, Sulzmann, and Wehr (1999a). Since then, it has been completed in a number of works (Sulzmann, Müller, and Zenger, 1999; Sulzmann, 2000; Pottier, 2001a;

Skalka and Pottier, 2002). Each of these presentations introduces minor variations. Here, we follow (Pottier, 2001a), which is itself inspired by (Sulzmann, Müller, and Zenger, 1999).

\section*{Definition}

Our presentation of $\operatorname{HM}(X)$ relies on the constraint language introduced in section 1.3. Technically, our approach of constraints is more direct than that of (Odersky, Sulzmann, and Wehr, 1999a). We interpret constraints within a model, give conjunction and existential quantification their standard meaning, and derive a number of equivalence laws (Section 1.3). Odersky et al., on the other hand, do not explicitly rely on a logical interpretation; instead, they axiomatize constraint equivalence, that is, they consider a number of equivalence laws as axioms. Thus, they ensure that their high-level proofs, such as type soundness and correctness and completeness of type inference, are independent of the low-level details of the logical interpretation of constraints. Their approach is also more general, since it allows dealing with other logical interpretations - such as "open-world" interpretations, where constraints are interpreted not within a fixed model, but within a family of extensions of a "current" model. In this chapter, we have avoided this extra layer of abstraction, for the sake of definiteness; however, the changes required to adopt Odersky et al.'s approach would not be extensive, since the forthcoming proofs do indeed rely mostly on constraint equivalence laws, rather than on low-level details of the logical interpretation of constraints.

Another slight departure from Odersky et al.'s work lies in the fact that we have enriched the constraint language with type scheme introduction and instantiation forms, which were absent in the original presentation of $\operatorname{HM}(X)$. To prevent this addition from affecting $\operatorname{HM}(X)$, we require the constraints that appear in $\operatorname{HM}(X)$ typing judgements to have no free program identifiers. Please note that this does not prevent them from containing let forms; we shall in fact exploit this feature when establishing an equivalence between $\operatorname{HM}(X)$ and the type system presented in section 1.5 , where the new constraint forms are effectively used.

The type system $\operatorname{HM}(X)$ consists of a four-place judgement whose parameters are a constraint $C$, an environment $\Gamma$, an expression $t$, and a type scheme $\sigma$. A judgement is written $C, \Gamma \vdash \mathrm{t}: \sigma$ and is read: under the assumptions $C$ and $\Gamma$, the expression $t$ has type $\sigma$. One may view $C$ as an assumption about the judgement's free type variables and $\Gamma$ as an assumption about t's free program identifiers. Please recall that $\Gamma$ now contains constrained type schemes, and that $\sigma$ is a constrained type scheme.

We would like the validity of a typing judgement to depend not on the

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-041.jpg?height=546&width=1516&top_left_y=227&top_left_x=237)

Figure 1-7: Typing rules for $\operatorname{HM}(X)$

syntax, but only on the meaning of its constraint assumption. We enforce this point of view by considering judgements equal modulo equivalence of their constraint assumptions. In other words, the typing judgements $C, \Gamma \vdash \mathrm{t}: \sigma$ and $D, \Gamma \vdash \mathrm{t}: \sigma$ are considered identical when $C \equiv D$ holds. As a result, it does not make sense to analyze the syntax of a judgement's constraint assumption. A judgement is valid, or holds, if and only if it is derivable via the rules given in Figure 1-7. Please note that a valid judgement may involve an unsatisfiable constraint. A program t is well-typed within the environment $\Gamma$ if and only if a judgement of the form $C, \Gamma \vdash \mathrm{t}: \sigma$ holds for some satisfiable constraint $C$.

Let us now explain the rules. Like DM-VAR, HMX-VAR looks up the environment to determine the type scheme associated with the program identifier $\mathrm{x}$. The constraint $C$ that appears in the conclusion must be strong enough to guarantee that $\sigma$ has an instance; this is expressed by the second premise. This technical requirement is used in the proof of Lemma 1.4.1. HMX-ABS, HMX-APP, and HMX-LET are identical to DM-ABS, DM-APP, and DM-LET, respectively, except that the assumption $C$ is made available to every subderivation. We recall that the type $\mathrm{T}$ may be viewed as the type scheme $\forall \varnothing$ [true].T (Definitions 1.2.18 and 1.3.2). As a result, types form a subset of type schemes, which implies that $\Gamma ; z: \mathrm{T}$ is a well-formed environment and $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ a well-formed typing judgement. To understand HMX-GEN, it is best to first consider the particular case where $C$ is true. This yields the following, simpler rule:

$$
\begin{equation*}
\frac{D, \Gamma \vdash \mathrm{t}: \mathrm{T} \quad \overline{\mathrm{x}} \# f t v(\Gamma)}{\exists \overline{\mathrm{x}} \cdot D, \Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{X}}[D] . \mathrm{T}} \tag{HMX-GEN'}
\end{equation*}
$$

The second premise is identical to that of DM-GEN: the type variables that are generalized must not occur free within the environment. The conclusion forms the type scheme $\forall \overline{\mathrm{X}}[D]$.T, where the type variables $\overline{\mathrm{X}}$ have become universally quantified, but are still subject to the constraint $D$. Please note that the type variables that occur free in $D$ may include not only $\overline{\mathrm{X}}$, but also other type variables, typically free in $\Gamma$. The rule's conclusion carries the constraint $\exists \overline{\mathrm{X}} . D$, thus recording the requirement that the newly formed type scheme should have an instance; again, this is used in the proof of Lemma 1.4.1. HMX-GEN may be viewed as a more liberal version of HMX-GEN', whereby part of the current constraint, namely $C$, need not be copied if it does not concern the type variables that are being generalized, namely $\overline{\mathrm{X}}$. This optimization is important in practice, because $C$ may be very large. An intuitive explanation for its correctness is given by the constraint equivalence law $\mathrm{C}$ LETAND, which expresses the same optimization in terms of let constraints. Because $\operatorname{HM}(X)$ does not use let constraints, the optimization is hard-wired into the typing rule. HMX-INST allows taking an instance of a type scheme. The reader may be surprised to find that, contrary to DM-INST, it does not involve a type substitution. Instead, the rule merely drops the universal quantifier, which amounts to applying the identity substitution $\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{X}}$. One should recall, however, that type schemes are considered equal modulo $\alpha$-conversion, so it is possible to rename the type scheme's universal quantifiers prior to using HMX-INST. The reason why this provides sufficient expressive power appears in the proof of Theorem 1.4.7 below. The constraint $D$ carried by the type scheme is recorded as part of the current constraint in HMX-INST's conclusion. The subsumption rule HMX-SUB allows a type $\mathrm{T}$ to be replaced at any time with an arbitrary supertype $\mathrm{T}^{\prime}$. Because both $\mathrm{T}$ and $\mathrm{T}^{\prime}$ may have free type variables, whether $\mathrm{T} \leq \mathrm{T}^{\prime}$ holds depends on the current assumption $C$, which is why the rule's second premise is an entailment assertion. An operational explanation of HMX-SUB is that it requires all uses of subsumption to be explicitly recorded in the current constraint. Please note that HMX-SUB remains a useful and necessary rule even when subtyping is interpreted as equality: then, it allows exploiting the type equations found in $C$. Last, HMXEXISTS allows the type variables that occur only within the current constraint to become existentially quantified. As a result, these type variables no longer occur free in the rule's conclusion; in other words, they have become local to the subderivation rooted at the premise. One may prove that the presence of HMX-EXISTS in the type system does not augment the set of well-typed programs, but does augment the set of valid typing judgements; it is a pleasant technical convenience. Indeed, because judgements are considered equal modulo constraint equivalence, constraints may be transparently simplified at any time. (By simplifying a constraint, we mean replacing it with an equiva-
lent constraint whose syntactic representation is considered simpler.) Bearing this fact in mind, one finds that an effect of rule HMX-Exists is to enable more simplifications: because constraint equivalence is a congruence, $C \equiv D$ implies $\exists \overline{\mathrm{X}} . C \equiv \exists \overline{\mathrm{X}} . D$, but the converse does not hold in general. For instance, there is in general no way of simplifying the judgement $\mathrm{X} \leq \mathrm{Y} \leq \mathrm{Z}, \Gamma \vdash \mathrm{t}: \sigma$, but if it is known that $\mathrm{Y}$ does not appear free in $\Gamma$ or $\sigma$, then HMX-EXISTS allows deriving $\exists \mathrm{Y} .(\mathrm{X} \leq \mathrm{Y} \leq \mathrm{Z}), \Gamma \vdash \mathrm{t}: \sigma$, which is the same judgement as $\mathrm{x} \leq \mathrm{Z}, \Gamma \vdash \mathrm{t}: \sigma$. Thus, an interesting simplification has been enabled. Please note that $\mathrm{X} \leq \mathrm{Y} \leq \mathrm{Z} \equiv \mathrm{X} \leq \mathrm{Z}$ does not hold, while, according to C-ExTRans, $\exists \mathrm{Y}$. $\mathrm{X} \leq \mathrm{Y} \leq \mathrm{Z}) \equiv \mathrm{X} \leq \mathrm{Z}$ does.

We now establish a few simple properties of the type system $\operatorname{HM}(X)$. Our first lemma is a minor technical property.

1.4.1 Lemma: $C, \Gamma \vdash \mathrm{t}: \sigma$ implies $C \Vdash \exists \sigma$.

The next lemma states that strengthening a judgement's constraint assumption preserves its validity. In other words, weakening a judgement preserves its validity. It is worth noting that in traditional presentations, which rely more heavily on type substitutions, the analogue of this result is a type substitution lemma; see for instance (Tofte, 1988, Lemma 2.7), (Leroy, 1992, Proposition 1.2), (Skalka and Pottier, 2002, Lemma 3.4). Here, the lemma further states that weakening a judgement does not alter the shape of its derivation, a useful property when reasoning by induction on type derivations.

1.4.2 Lemma [Weakening]: If $C^{\prime} \Vdash C$, then every derivation of $C, \Gamma \vdash \mathrm{t}: \sigma$ may be turned into a derivation of $C^{\prime}, \Gamma \vdash \mathrm{t}: \sigma$ with the same shape.

Proof: The proof is by structural induction on a derivation of $C, \Gamma \vdash \mathrm{t}: \sigma$. In each proof case, we adopt the notations of Figure 1-7.
- Case HMX-VAR. The rule's conclusion is $C, \Gamma \vdash \mathrm{x}: \sigma$. Its premises are $\Gamma(\mathrm{x})=\sigma$ (1) and $C \Vdash \exists \sigma$ (2). By hypothesis, we have $C^{\prime} \Vdash C$ (3). By transitivity of entailment, (3) and (2) imply $C^{\prime} \Vdash \exists \sigma$ (4). By HMX-VAR, (1) and (4) yield $C^{\prime}, \Gamma \vdash \mathrm{x}: \sigma$.
- Cases HMX-ABS, HMX-App, HMX-LET. By the induction hypothesis and by HMX-ABS, HMX-APP, or HMX-LET, respectively.
- Case HMX-GEn. The rule's conclusion is $C \wedge \exists \overline{\mathrm{x}} . D, \Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{x}}[D]$.T. Its premises are $C \wedge D, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (1) and $\overline{\mathrm{x}} \# f t v(C, \Gamma)$ (2). By hypothesis, we have $C^{\prime} \Vdash C \wedge \exists \overline{\mathrm{X}} . D$ (3). We may assume, w.l.o.g., $\overline{\mathrm{X}} \# \mathrm{ftv}\left(C^{\prime}\right)$ (4). Applying the induction hypothesis to (1) and to the entailment assertion $C^{\prime} \wedge C \wedge D \Vdash C \wedge D$, we obtain $C^{\prime} \wedge C \wedge D, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (5). By HMX-GEN, applied to (5), (2) and (4), we get $C^{\prime} \wedge C \wedge \exists \overline{\mathrm{x}} . D, \Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{x}}[D] . \mathrm{T}$ (6). By (3) and C-Dup, the constraints $C^{\prime} \wedge C \wedge \exists \overline{\mathrm{x}} . D$ and $C^{\prime}$ are equivalent, so (6) is the goal $C^{\prime}, \Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{x}}[D]$. .T.
- Case HmX-Inst. The rule's conclusion is $C \wedge D, \Gamma \vdash \mathrm{t}$ : T. Its premise is $C, \Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{X}}[D] . \mathrm{T}$ (1). By hypothesis, $C^{\prime}$ entails $C \wedge D$ (2). Because (2) implies $C^{\prime} \Vdash C$, the induction hypothesis may be applied to (1), yielding $C^{\prime}, \Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{x}}[D] . \mathrm{T}$ (3). By HmX-Inst, we obtain $C^{\prime} \wedge D, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (4). Because (2) implies $C^{\prime} \equiv C^{\prime} \wedge D$, (4) is the goal $C^{\prime}, \Gamma \vdash \mathrm{t}: \mathrm{T}$.
- Case HmX-Sub. The rule's conclusion is $C, \Gamma \vdash \mathrm{t}: \mathrm{T}^{\prime}$. Its premises are $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (1) and $C \Vdash \mathrm{T} \leq \mathrm{T}^{\prime}$ (2). By hypothesis, we have $C^{\prime} \Vdash C$ (3). Applying the induction hypothesis to (1) and (3) yields $C^{\prime}, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (4). By transitivity of entailment, (3) and (2) imply $C^{\prime} \Vdash \mathrm{T} \leq \mathrm{T}^{\prime}$ (5). By HMX-SuB, (4) and (5) yield $C^{\prime}, \Gamma \vdash \mathrm{t}: \mathrm{T}^{\prime}$.
- Case HmX-Exists. The rule's conclusion is $\exists \overline{\mathrm{x}} . C, \Gamma \vdash \mathrm{t}: \sigma$. Its premises are $C, \Gamma \vdash \mathrm{t}: \sigma(\mathbf{1})$ and $\overline{\mathrm{x}} \# f t v(\Gamma, \sigma)(\mathbf{2})$. By hypothesis, we have $C^{\prime} \Vdash$ $\exists \overline{\mathrm{X}} . C$ (3). We may assume, w.l.o.g., $\overline{\mathrm{x}} \# \mathrm{ftv}\left(C^{\prime}\right)$ (4). Applying the induction hypothesis to (1) and to the entailment assertion $C^{\prime} \wedge C \Vdash C$, we obtain $C^{\prime} \wedge C, \Gamma \vdash \mathrm{t}: \sigma$ (5). By HmX-Exists, (5) and (2) yield $\exists \overline{\mathrm{X}} .\left(C^{\prime} \wedge C\right), \Gamma \vdash$ $\mathrm{t}: \sigma$ (6). By (4) and C-ExAnd, the constraint $\exists \overline{\mathrm{X}}$. $\left(C^{\prime} \wedge C\right)$ is equivalent to $C^{\prime} \wedge \exists \overline{\mathrm{X}}$. $C$, which, by (3) and C-Dup, is equivalent to $C^{\prime}$. Thus, (6) is the goal $C^{\prime}, \Gamma \vdash \mathrm{t}: \sigma$.

We do not give a direct type soundness proof for $\operatorname{HM}(X)$. Instead, in section 1.5 , we prove that it is equivalent to another type system, which later is itself proven sound. A direct type soundness result, based on a denotational semantics, may be found in (Odersky, Sulzmann, and Wehr, 1999a). Another type soundness proof, which follows Wright and Felleisen's syntactic approach (1994b), appears in (Skalka and Pottier, 2002). Last, a hybrid approach, which combines some of the advantages of the previous two, is given in (Pottier, 2001a).

\section*{An alternate presentation of $\mathrm{HM}(\boldsymbol{X})$}

The presentation of $\mathrm{HM}(X)$ given in Figure 1-7 has only four syntax-directed rules out of eight. It is a good specification of the type system, but it is far from an algorithmic description. As a first step towards such a description, we provide an alternate presentation of $\operatorname{HM}(X)$, where generalization is performed only at let expressions and instantiation takes place only at references to program identifiers (Figure 1-8). It has the property that all judgements are of the form $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$, rather than $C, \Gamma \vdash \mathrm{t}: \sigma$. The following theorem states that the two presentations are indeed equivalent.

1.4.3 Theorem: $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ is derivable via the rules of Figure 1-8 if and only if it is a valid $\operatorname{HM}(X)$ judgement.

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-045.jpg?height=493&width=1502&top_left_y=233&top_left_x=239)

Figure 1-8: An alternate presentation of $\mathbf{H M}(X)$

This theorem shows that the rule sets of Figures 1-7 and 1-8 derive the same monomorphic judgements, that is, the same judgements of the form $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$. The fact that judgements of the form $C, \Gamma \vdash \mathrm{t}: \sigma$, where $\sigma$ is a not a monotype, cannot be derived using the new rule set is a technical simplification, without deep significance; the first two exercises below shed some light on this issue.

1.4.4 EXERCISE $[\star \star]$ : Show that both rule sets lead to the same set of well-typed programs.

1.4.5 ExERcISE $[\star \star$ ]: Show that, if HMX-GEN is added to the rule set of Figure 18 , then both rule sets derive exactly the same judgements.

1.4.6 EXERCISE $[\star \star \star, \nrightarrow]$ : Show that it is possible to simplify the presentation of Damas and Milner's type system in an analogous manner. That is, define an alternate set of typing rules for DM, which allows deriving judgements of the form $\Gamma \vdash \mathrm{t}: \mathrm{T}$; then, show that this new rule set is equivalent to the previous one, in the same sense as above. Which auxiliary properties of DM does your proof require? A solution is given in (Clément, Despeyroux, Despeyroux, and Kahn, 1986).

\section*{Relating $\mathrm{HM}(X)$ with Damas and Milner's type system}

In order to explain our interest in $\operatorname{HM}(X)$, we wish to show that it is more general than Damas and Milner's type system. Since $\operatorname{HM}(X)$ really is a family of type systems, we must make this statement more precise. First, every member of the $\mathrm{HM}(X)$ family contains DM. Conversely, DM contains $\mathrm{HM}(=)$, the
constraint-based type system obtained by specializing $\operatorname{HM}(X)$ to the setting of an equality-only syntactic model.

The first of these assertions is easy to prove, because the mapping from DM judgements to $\operatorname{HM}(X)$ judgements is essentially the identity: every valid DM judgement may be viewed as a valid $\operatorname{HM}(X)$ judgement under the trivial assumption true. This statement relies on the fact that the DM type scheme $\forall \overline{\mathrm{X}}$. $\mathrm{T}$ is identified with the constrained type scheme $\forall \overline{\mathrm{X}}$ [true].T, so DM type schemes (resp. environments) form a subset of $\operatorname{HM}(X)$ type schemes (resp. environments). Its proof is routine, except perhaps in the case of DM-INST, where it is shown how the effect of applying a substitution in DM is emulated by strengthening the current constraint in $\operatorname{HM}(X)$.

1.4.7 Theorem: If $\Gamma \vdash \mathrm{t}: \mathrm{S}$ holds in $\mathrm{DM}$, then true, $\Gamma \vdash \mathrm{t}: \mathrm{S}$ holds in $\operatorname{HM}(X)$.

Proof: The proof is by structural induction on a derivation of $\Gamma \vdash t: S$. In each proof case, we adopt the notations of Figure 1-3.
- Case DM-VAR. The rule's conclusion is $\Gamma \vdash \mathrm{x}: \mathrm{S}$. Its premise is $\Gamma(\mathrm{x})=$ $\mathrm{S}$ (1). By definition and by $\mathrm{C}-\mathrm{Ex} *$, the constraint $\exists \mathrm{S}$ is equivalent to true. By applying HMX-VAR to (1) and to the assertion true $\Vdash$ true, we obtain true, $\Gamma \vdash \mathrm{x}: \mathrm{S}$.
- Cases DM-ABS, DM-ApP, DM-LET. By the induction hypothesis and by HMX-ABS, HMX-APP or HMX-LET, respectively.

$\circ$ Case DM-GEn. The rule's conclusion is $\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{x}}$.T. Its premises are $\Gamma \vdash \mathrm{t}: \mathrm{T}(\mathbf{1})$ and $\overline{\mathrm{X}} \# \mathrm{ftv}(\Gamma)$ (2). Applying the induction hypothesis to (1) yields true, $\Gamma \vdash \mathrm{t}: \mathrm{T}$ (3). Furthermore, (2) implies $\overline{\mathrm{X}} \# \mathrm{ftv}(\mathrm{true}, \Gamma)$ (4). By HMX-GEN, (3) and (4) yield true, $\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{x}}[$ true].T.
- Case Dm-Inst. The rule's conclusion is $\Gamma \vdash \mathrm{t}:[\overrightarrow{\mathrm{x}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$. Its premise is $\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{X}} . \mathrm{T}$ (1). We may assume, w.l.o.g., $\overline{\mathrm{X}} \# \mathrm{ftv}(\Gamma, \overline{\mathrm{T}})$ (2). Applying the induction hypothesis to (1) yields true, $\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{X}}[$ true].T (3). By HMXInst, (3) implies true, $\Gamma \vdash \mathrm{t}: \mathrm{T}$ (4). By Lemma 1.4.2, we may weaken this judgement so as to obtain $\overrightarrow{\mathrm{x}}=\overrightarrow{\mathrm{T}}, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (5). Using C-EQ, C-ExTrans, and C-ExAnd, it is possible to establish $\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}} \Vdash \mathrm{T}=[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$ (6). Applying HMX-SuB to (5) and (6), we find $\overrightarrow{\mathrm{x}}=\overrightarrow{\mathrm{T}}, \Gamma \vdash \mathrm{t}:[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$ (7). Last, (2) implies $\overline{\mathrm{X}} \# f t v(\Gamma,[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T})$ (8). Applying HMX-EXisTs to (7) and (8), we obtain $\exists \overline{\mathrm{X}} .(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}), \Gamma \vdash \mathrm{t}:[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$ (9). By (2) and C-NAME, the constraint $\exists \overline{\mathrm{X}} .(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$ is equivalent to true, so (9) is the goal.

We are now interested in proving that $\mathrm{HM}(=)$, as defined above, is contained within DM. To this end, we must translate every $\mathrm{HM}(=)$ judgement to a DM judgement. It quickly turns out that this is possible if the original judgement's constraint assumption is satisfiable.

We begin by explaining how an $\mathrm{HM}(=)$ is translated into a DM type scheme. Such a translation is made possible by the fact that the definition of $\operatorname{HM}(=)$ assumes an equality-only syntactic model. Indeed, in that setting, every satisfiable constraint admits a most general unifier (Definition 1.3.41), whose properties we make essential use of.

In fact, we must not only translate a type scheme, but also apply a type substitution to it. Instead of separating these steps, we perform both at once, and parameterize the translation by a type substitution $\theta$. (It does not appear that separating them would help.) The definition of $\llbracket \sigma \rrbracket_{\theta}$ is somewhat involved: it is given in the statement of the following lemma, whose proof establishes that the definition is indeed well-formed.

1.4.8 Lemma: Consider a type scheme $\sigma$ and an idempotent type substitution $\theta$ such that $f t v(\sigma) \subseteq \operatorname{dom}(\theta)$ (1) and $\exists \theta \Vdash \exists \sigma$ (2). Write $\sigma=\forall \overline{\mathrm{x}}[D]$.T, where $\overline{\mathrm{x}} \# \theta$ (3). Then, there exists a type substitution $\theta^{\prime}$ such that $\theta^{\prime}$ extends $\theta, \operatorname{dom}\left(\theta^{\prime}\right)$ is $\operatorname{dom}(\theta) \cup \overline{\mathrm{X}}$, and $\theta^{\prime}$ is a most general unifier of $\exists \theta \wedge D$. Let $\overline{\mathrm{Y}}=f \operatorname{tv}\left(\theta^{\prime}(\overline{\mathrm{X}})\right) \backslash \operatorname{range}(\theta)$. Then, the translation of $\sigma$ under $\theta$, written $\llbracket \sigma \rrbracket_{\theta}$, is the DM type scheme $\forall \overline{\mathrm{Y}} \cdot \theta^{\prime}(\mathrm{T})$. This is a well-formed definition. Furthermore, $f t v\left(\llbracket \sigma \rrbracket_{\theta}\right) \subseteq \operatorname{range}(\theta)$ holds.

Proof: By (2), $\exists \theta$ is equivalent to $\exists \theta \wedge \exists \sigma$, which may be written $\exists \theta \wedge \exists \overline{\mathrm{X}} . D$. By (3) and C-ExAnd, this is $\exists \overline{\mathrm{x}}$. $(\exists \theta \wedge D)$. Thus, because $\theta$ is a most general unifier of $\exists \theta, \theta$ is also a most general unifier of $\exists \overline{\mathrm{X}}$. $(\exists \theta \wedge D)$ (4). Furthermore, $\operatorname{ftv}(\exists \overline{\mathrm{X}} .(\exists \theta \wedge D))$ is $\operatorname{ftv}(\exists \theta \wedge \exists \sigma)$, which by definition of $\exists \theta$ and by (1) is a subset of $\operatorname{dom}(\theta)(\mathbf{5})$. By (4), (3), (5), and Lemma 1.3.45, there exists a type substitution $\theta^{\prime}$ such that $\theta^{\prime}$ extends $\theta(6)$ and $\theta^{\prime}$ is a most general unifier of $\exists \theta \wedge D(\mathbf{7})$ and $\operatorname{dom}\left(\theta^{\prime}\right)=\operatorname{dom}(\theta) \cup \overline{\mathrm{X}}(\mathbf{8})$.

Let us now define $\overline{\mathrm{Y}}=f t v\left(\theta^{\prime}(\overline{\mathrm{X}})\right) \backslash \operatorname{range}(\theta)$ and $\llbracket \sigma \rrbracket_{\theta}=\forall \overline{\mathrm{Y}} \cdot \theta^{\prime}(\mathrm{T})$. By (1), we have $f t v(\mathrm{~T}) \subseteq \overline{\mathrm{X}} \cup \operatorname{dom}(\theta)$. Applying $\theta^{\prime}$ and exploiting (6), we find $f t v\left(\theta^{\prime}(\mathrm{T})\right) \subseteq$ $f t v\left(\theta^{\prime}(\overline{\mathrm{X}})\right) \cup \operatorname{range}(\theta)$, which by definition of $\overline{\mathrm{Y}}$ may be written $f t v\left(\theta^{\prime}(\mathrm{T})\right) \subseteq$ $\overline{\mathrm{Y}} \cup$ range $(\theta)$. Subtracting $\overline{\mathrm{Y}}$ on each side, we find $\operatorname{ftv}\left(\llbracket \sigma \rrbracket_{\theta}\right) \subseteq \operatorname{range}(\theta) \mathbf{( 9 )}$.

To show that the definition of $\llbracket \sigma \rrbracket_{\theta}$ is valid, there remains to show that it does not depend on the choice of $\overline{\mathrm{X}}$ or $\theta^{\prime}$. To prove the former, it suffices to establish $\overline{\mathrm{X}} \# \mathrm{ftv}\left(\llbracket \sigma \rrbracket_{\theta}\right)$, which indeed follows from (3) and (9). As for the latter, because of the constraints imposed by (6), (7), and (8), and by Lemma 1.3.44, distinct choices of $\theta^{\prime}$ may differ only by a renaming of $f t v\left(\theta^{\prime}(\overline{\mathrm{X}})\right) \backslash \operatorname{range}(\theta)$, that is, $\overline{\mathrm{Y}}$. So, we must check $\overline{\mathrm{Y}} \# \mathrm{ftv}\left(\llbracket \sigma \rrbracket_{\theta}\right)$, which holds by definition.

Please note that if $\sigma$ is in fact a type $\mathrm{T}$, where $f t v(\mathrm{~T}) \subseteq \operatorname{dom}(\theta)$, then $\overline{\mathrm{X}}$ is empty, so $\theta^{\prime}$ is $\theta, \overline{\mathrm{Y}}$ is empty, and $\llbracket \mathrm{T} \rrbracket_{\theta}=\theta(\mathrm{T})$. In other words, the translation of a type under $\theta$ is its image through $\theta$. More generally, the translation of an unconstrained type scheme (that is, a type scheme whose constraint is true) is its image through $\theta$, as stated by the following exercise.

1.4.9 EXERCISE $[\star \star, \nrightarrow]$ : Prove that $\llbracket \forall \overline{\mathrm{X}} . \mathrm{T} \rrbracket_{\theta}$, when defined, is $\theta(\forall \overline{\mathrm{X}} . \mathrm{T})$.

The translation becomes more than a mere type substitution when applied to a nontrivial constrained type scheme. Some examples of this situation are given below.

1.4.10 Example: Let $\sigma=\forall \mathrm{XY}[\mathrm{X}=\mathrm{Y} \rightarrow \mathrm{Y}]$.X. Let $\theta$ be the identity substitution. The type scheme $\sigma$ is closed and the constraint $\exists \sigma$ is equivalent to true, so $\llbracket \sigma \rrbracket_{\theta}$ is defined. We must find a type substitution $\theta^{\prime}$ whose domain is XY and that is a most general unifier of $X=Y \rightarrow Y$. All such substitutions are of the form $[\mathrm{X} \mapsto(\mathrm{Z} \rightarrow \mathrm{Z}), \mathrm{Y} \mapsto \mathrm{Z}]$, where $\mathrm{Z}$ is fresh. We have $f t v\left(\theta^{\prime}(\mathrm{XY})\right)=\mathrm{Z}$, whence $\llbracket \sigma \rrbracket_{\theta}=\forall \mathrm{Z} . \mathrm{Z} \rightarrow \mathrm{Z}$. Note that the choice of $\mathrm{Z}$ does not matter, since it is bound in $\llbracket \sigma \rrbracket_{\theta}$. Roughly speaking, the effect of the translation was to replace the body $\mathrm{X}$ of the constrained type scheme with its most general solution under the constraint $\mathrm{X}=\mathrm{Y} \rightarrow \mathrm{Y}$.

Let $\sigma=\forall \mathrm{XY}_{1}\left[\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}\right]$.X. Let $\theta=\left[\mathrm{Y}_{2} \mapsto \mathrm{Z}_{2}\right]$. We have $f t v(\sigma)=$ $\mathrm{Y}_{2} \subseteq \operatorname{dom}(\theta)$. The constraint $\exists \sigma$ is equivalent to true, so $\llbracket \sigma \rrbracket_{\theta}$ is defined. We must find a type substitution $\theta^{\prime}$ whose domain is $\mathrm{XY}_{1} \mathrm{Y}_{2}$ that extends $\theta$ and that is a most general unifier of $\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}$. All such substitutions are of the form $\left[\mathrm{X} \mapsto\left(\mathrm{Z}_{1} \rightarrow \mathrm{Z}_{2}\right), \mathrm{Y}_{1} \mapsto \mathrm{Z}_{1}, \mathrm{Y}_{2} \mapsto \mathrm{Z}_{2}\right]$, where $\mathrm{Z}_{1}$ is fresh. We have $\operatorname{ftv}\left(\theta^{\prime}\left(\mathrm{XY}_{1}\right)\right) \backslash \operatorname{range}(\theta)=\mathrm{Z}_{1} \mathrm{Z}_{2} \backslash \mathrm{Z}_{2}=\mathrm{Z}_{1}$, whence $\llbracket \sigma \rrbracket_{\theta}=\forall \mathrm{Z}_{1} \cdot \mathrm{Z}_{1} \rightarrow \mathrm{Z}_{2}$. The type variable $\mathrm{Z}_{2}$ is not universally quantified - even though it appears in the image of $\mathrm{X}$, which was universally quantified in $\sigma$-because $\mathrm{Z}_{2}$ is the image of $\mathrm{Y}_{2}$, which was free in $\sigma$.

Before attacking the main theorem, let us establish a couple of technical properties of the translation. First, $\llbracket \sigma \rrbracket_{\theta}$ is insensitive to the behavior of $\theta$ outside $\operatorname{ftv}(\sigma)$, a natural property, since our informal intent is for $\theta$ to be applied to $\sigma$.

1.4.11 Lemma: If $\theta_{1}$ and $\theta_{2}$ coincide on $f t v(\sigma)$, then $\llbracket \sigma \rrbracket_{\theta_{1}}$ and $\llbracket \sigma \rrbracket_{\theta_{2}}$ are either both undefined, or both defined and identical.

Second, if $C \Vdash \sigma \preceq \mathrm{T}^{\prime}$ holds, then the translations of $\sigma$ and $\mathrm{T}^{\prime}$ under a most general unifier of $C$ are in Damas and Milner's instance relation. One might say, roughly speaking, that the instance relation is preserved by the translation.

1.4.12 Lemma: Let $f t v\left(\sigma, \mathrm{T}^{\prime}\right) \subseteq \operatorname{dom}(\theta)$ (1) and $\exists \theta \Vdash \exists \sigma$ (2). Let $\exists \theta \Vdash \sigma \preceq \mathrm{T}^{\prime}$ (3). Then, $\theta\left(\mathrm{T}^{\prime}\right)$ is an instance of the DM type scheme $\llbracket \sigma \rrbracket_{\theta}$.

Proof: Write $\sigma=\forall \overline{\mathrm{X}}[D] . \mathrm{T}$, where $\overline{\mathrm{X}} \# \theta$ (4) and $\overline{\mathrm{X}} \# f t v\left(\mathrm{~T}^{\prime}\right)$ (5). By (1), $(2)$, and (4), one may define $\theta^{\prime}, \overline{\mathrm{Y}}$, and $\llbracket \sigma \rrbracket_{\theta}$ exactly as in the statement of Lemma 1.4.8. By (5) and Definition 1.3.3, (3) is synonymous with $\exists \theta \Vdash \exists \overline{\mathrm{X}}$.( $D \wedge$
$\mathrm{T}=\mathrm{T}^{\prime}$ ). Reasoning in the same manner as in the first paragraph of the proof of Lemma 1.4.8, we find that there exists a type substitution $\theta^{\prime \prime}$ such that $\theta^{\prime \prime}$ extends $\theta, \operatorname{dom}\left(\theta^{\prime \prime}\right)$ is $\operatorname{dom}(\theta) \cup \overline{\mathrm{X}}$, and $\theta^{\prime \prime}$ is a most general unifier of $\exists \theta \wedge D \wedge \mathrm{T}=\mathrm{T}^{\prime}$.

We have $\operatorname{dom}\left(\theta^{\prime}\right)=\operatorname{dom}\left(\theta^{\prime \prime}\right)(\mathbf{6})$. Furthermore, $\theta^{\prime}$ is a most general unifier of $\exists \theta \wedge D$, while $\theta^{\prime \prime}$ is a most general unifier of $\exists \theta \wedge D \wedge \mathrm{T}=\mathrm{T}^{\prime}$, which implies $\exists \theta^{\prime \prime} \Vdash \exists \theta^{\prime}(\mathbf{7})$. By Lemma 1.3.39, $\theta^{\prime \prime}$ refines $\theta^{\prime}$. That is, there exists a type substitution $\varphi$ such that $\theta^{\prime \prime}$ is the restriction of $\varphi \circ \theta^{\prime}$ to $\operatorname{dom}(\theta) \cup \overline{\mathrm{x}}(\mathbf{8})$. We may require $\operatorname{dom}(\varphi) \subseteq \operatorname{range}(\theta) \cup f t v\left(\theta^{\prime}(\overline{\mathrm{X}})\right)(\mathbf{9})$ without compromising (8).

Consider $\mathrm{X} \in \operatorname{dom}(\theta)$. Because $\theta^{\prime \prime}$ extends $\theta$, we have $\theta^{\prime \prime}(\mathrm{X})=\theta(\mathrm{X})(\mathbf{1 0})$. Furthermore, by (8), we have $\theta^{\prime \prime}(\mathrm{X})=\left(\varphi \circ \theta^{\prime}\right)(\mathrm{x})=(\varphi \circ \theta)(\mathrm{X})(\mathbf{1 1})$. Using (10) and (11), we find $\theta(\mathrm{X})=\varphi(\theta(\mathrm{X}))$. Because this holds for every $\mathrm{X} \in \operatorname{dom}(\theta)$, $\varphi$ must be the identity over range $(\theta)$; that is, $\operatorname{dom}(\varphi)$ \# range $(\theta)$ (12) holds. Combining (9) and (12), we find $\operatorname{dom}(\varphi) \subseteq f t v\left(\theta^{\prime}(\overline{\mathrm{X}})\right) \backslash \operatorname{range}(\theta)$, that is, $\operatorname{dom}(\varphi) \subseteq \overline{\mathrm{Y}}(\mathbf{1 3})$.

By construction of $\theta^{\prime \prime}$, we have $\exists \theta^{\prime \prime} \Vdash \mathrm{T}=\mathrm{T}^{\prime}$. By Lemma 1.3.29, this implies $\theta^{\prime \prime}\left(\exists \theta^{\prime \prime}\right) \Vdash \theta^{\prime \prime}(\mathrm{T})=\theta^{\prime \prime}\left(\mathrm{T}^{\prime}\right)$, which by Lemma 1.3.42 may be read true $\Vdash \theta^{\prime \prime}(\mathrm{T})=$ $\theta^{\prime \prime}\left(\mathrm{T}^{\prime}\right)$. By Lemma 1.3.32, $\theta^{\prime \prime}(\mathrm{T})$ and $\theta^{\prime \prime}\left(\mathrm{T}^{\prime}\right)$ coincide. Because by (1) $f t v(\mathrm{~T})$ is a subset of $\operatorname{dom}(\theta) \cup \overline{\mathrm{X}}$ and by (8), the former may be written $\varphi\left(\theta^{\prime}(\mathrm{T})\right)$. By (1) and because $\theta^{\prime \prime}$ extends $\theta$, the latter is $\theta\left(\mathrm{T}^{\prime}\right)$. Thus, we have $\varphi\left(\theta^{\prime}(\mathrm{T})\right)=\theta\left(\mathrm{T}^{\prime}\right)$. Together with (13), this establishes that $\theta\left(\mathrm{T}^{\prime}\right)$ is an instance of $\forall \overline{\mathrm{Y}} . \theta^{\prime}(\mathrm{T})$, that is, $\llbracket \sigma \rrbracket_{\theta}$.

We extend the translation to environments as follows. $\llbracket \varnothing \rrbracket_{\theta}$ is $\varnothing$. If $\exists \theta \Vdash \exists \sigma$ holds, then $\llbracket \Gamma ; \mathrm{x}: \sigma \rrbracket_{\theta}$ is $\llbracket \Gamma \rrbracket_{\theta} ; \mathrm{x}: \llbracket \sigma \rrbracket_{\theta}$, otherwise it is $\llbracket \Gamma \rrbracket_{\theta}$. Notice that $\llbracket \Gamma \rrbracket_{\theta}$ contains fewer bindings than $\Gamma$, which ensures that bindings $x: \sigma$ for which $\exists \theta \Vdash \exists \sigma$ does not hold will not be used in the translation. Please note that $\llbracket \Gamma \rrbracket_{\theta}$ is defined when $f t v(\Gamma) \subseteq \operatorname{dom}(\theta)$ holds.

We are now ready to prove the main theorem. Please note that, by requiring $\theta$ to be a most general unifier of $C$, we also require $C$ to be satisfiable. Judgements that carry an unsatisfiable constraint cannot be translated.

1.4.13 Theorem: Let $C, \Gamma \vdash \mathrm{t}: \sigma$ hold in $\operatorname{HM}(=)$. Let $\theta$ be a most general unifier of $C$ such that $f t v(\Gamma, \sigma) \subseteq \operatorname{dom}(\theta)$. Then, $\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{t}: \llbracket \sigma \rrbracket_{\theta}$ holds in DM.

Proof: Let us first remark that, by Lemma 1.4.1, we have $C \Vdash \exists \sigma$. This may be written $\exists \theta \Vdash \exists \sigma$, which guarantees that $\llbracket \sigma \rrbracket_{\theta}$ is defined. The proof is by structural induction on an $\operatorname{HM}(=)$ typing derivation. We assume that the derivation is expressed in terms of the rules of Figure 1-8, but split HMDLETGEN into HMX-LET and HMX-GEN for the sake of readability.
- Case HmD-VARInst. The rule's conclusion is $C \wedge D, \Gamma \vdash \mathrm{x}: \mathrm{T}$. By hypothesis, $\theta$ is a most general unifier of $C \wedge D(\mathbf{1})$, and $\operatorname{ftv}(\mathrm{T}) \subseteq \operatorname{dom}(\theta)$ (2)
holds. The rule's premise is $\Gamma(\mathrm{x})=\sigma$ (3), where $\sigma$ stands for $\forall \overline{\mathrm{x}}[D]$.T. By (1), we have $\exists \theta \equiv C \wedge D \Vdash D \Vdash \exists \overline{\mathrm{x}} . D \equiv \exists \sigma$ (4). Furthermore, we have $f t v(\sigma) \subseteq f t v(\Gamma) \subseteq \operatorname{dom}(\theta)$ (5). These facts show that $\llbracket \sigma \rrbracket_{\theta}$ is defined. Together with (3), this implies $\llbracket \Gamma \rrbracket_{\theta}(\mathrm{x})=\llbracket \sigma \rrbracket_{\theta}$. By DM-VAR, $\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{x}: \llbracket \sigma \rrbracket_{\theta}$ (6) follows. Now, by Lemma 1.3.19, we have $D \Vdash \sigma \preceq \mathrm{T}$, which, combined with $\exists \theta \Vdash D$, yields $\exists \theta \Vdash \sigma \preceq \mathrm{T}$ (7). By (7), (4), (5), (2), and Lemma 1.4.12, we find that $\theta(\mathrm{T})$ is an instance of $\llbracket \sigma \rrbracket_{\theta}$. Thus, applying DM-INsT to (6) yields $\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{t}: \theta(\mathrm{T})$.
- Case HmD-ABs. The rule's conclusion is $C, \Gamma \vdash \lambda z . t: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$. Its premise is $C,(\Gamma ; \mathrm{z}: \mathrm{T}) \vdash \mathrm{t}: \mathrm{T}^{\prime}$. Applying the induction hypothesis to it yields $\llbracket \Gamma \rrbracket_{\theta} ; \mathrm{z}$ : $\theta(\mathrm{T}) \vdash \mathrm{t}: \theta\left(\mathrm{T}^{\prime}\right)$. By DM-ABS, this implies $\llbracket \Gamma \rrbracket_{\theta} \vdash \lambda$ z.t $: \theta(\mathrm{T}) \rightarrow \theta\left(\mathrm{T}^{\prime}\right)$, that is, $\llbracket \Gamma \rrbracket_{\theta} \vdash \lambda z . t: \theta\left(\mathrm{T} \rightarrow \mathrm{T}^{\prime}\right)$.
- Case HMd-Apr. By an extension of $\operatorname{dom}(\theta)$ to include $f t v(T)$, by the induction hypothesis, and by DM-APP.
- Case HMX-Let. By an extension of $\operatorname{dom}(\theta)$ to include $f t v(\sigma)$, by the induction hypothesis, and by DM-LET.
- Case HmX-GEn. The rule's conclusion is $C \wedge \exists \sigma, \Gamma \vdash \mathrm{t}: \sigma$, where $\sigma$ stands for $\forall \overline{\mathrm{X}}[D]$.T. By hypothesis, $\theta$ is a most general unifier of $C \wedge \exists \sigma$ (1), and $f t v(\Gamma, \sigma) \subseteq \operatorname{dom}(\theta) \mathbf{( 2 )}$ holds. The rule's premises are $C \wedge D, \Gamma \vdash \mathrm{t}: \mathrm{T}(\mathbf{3})$ and $\overline{\mathrm{X}} \# \mathrm{ftv}(C, \Gamma)$ (4). We may further assume, w.l.o.g., $\overline{\mathrm{X}} \# \theta$ (5). Given (1), (2), and (5), we may define $\theta^{\prime}$ and $\bar{Y}$ exactly as in Lemma 1.4.8. Then, $\theta^{\prime}$ is a most general unifier of $\exists \theta \wedge D$, that is, $C \wedge D$. Furthermore, $\operatorname{dom}\left(\theta^{\prime}\right)$ is $\operatorname{dom}(\theta) \cup \overline{\mathrm{x}}$, which by (2) is a superset of $f t v(\Gamma, \mathrm{T})$. Thus, the induction hypothesis applies to $\theta^{\prime}$ and to (3), yielding $\llbracket \Gamma \rrbracket_{\theta^{\prime}} \vdash \mathrm{t}: \theta^{\prime}(\mathrm{T})$. Because $\theta^{\prime}$ extends $\theta$, by (2) and by Lemma 1.4.11, this may be read $\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{t}: \theta^{\prime}(\mathrm{T})$ (6). According to Lemma 1.4.8, we have $f t v\left(\llbracket \Gamma \rrbracket_{\theta}\right) \subseteq$ range $(\theta)$, which by construction of $\bar{Y}$ implies $\overline{\mathrm{Y}} \# \operatorname{ftv}\left(\llbracket \Gamma \rrbracket_{\theta}\right)$ (7). By DM-GEN, (6) and (7) yield $\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{t}: \forall \overline{\mathrm{Y}} \cdot \theta^{\prime}(\mathrm{T})$, that is, $\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{t}: \llbracket \sigma \rrbracket_{\theta}$.
- Case HmD-Sub. The rule's conclusion is $C, \Gamma \vdash \mathrm{t}: \mathrm{T}^{\prime}$. By hypothesis, $\theta$ is a most general unifier of $C \mathbf{( 1 )}$, and $f t v\left(\Gamma, \mathrm{T}^{\prime}\right) \subseteq \operatorname{dom}(\theta)$ (2) holds. The goal is $\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{t}: \theta\left(\mathrm{T}^{\prime}\right)(\mathbf{3})$. The rule's premises are $C, \Gamma \vdash \mathrm{t}: \mathrm{T} \mathbf{( 4 )}$ and $C \Vdash \mathrm{T}=\mathrm{T}^{\prime}$ (5). We may assume, w.l.o.g., ftv $(\mathrm{T}) \# \operatorname{range}(\theta)$ (6). Then, by (6) and Lemma 1.3.43, we may extend the domain of $\theta$, so as to achieve $f t v(\mathrm{~T}) \subseteq \operatorname{dom}(\theta)(7)$, without compromising (1) or (2) or affecting the goal (3). By (1), (2), and (7), the induction hypothesis applies to (4), yielding $\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{t}: \theta(\mathrm{T})(8)$. Now, thanks to (1), (5) may be $\operatorname{read} \exists \theta \Vdash \mathrm{T}=\mathrm{T}^{\prime}$, which by Lemmas 1.3 .29 and 1.3.42 implies true $\Vdash \theta(\mathrm{T})=\theta\left(\mathrm{T}^{\prime}\right)$. Then, Lemma 1.3.32 shows that $\theta(\mathrm{T})$ and $\theta\left(\mathrm{T}^{\prime}\right)$ coincide. As a result, (8) is the goal (3).

$\circ$ Case HmD-ExisTs. The rule's conclusion is $\exists \overline{\mathrm{X}} . C, \Gamma \vdash \mathrm{t}$ : T. By hypothesis, $\theta$ is a most general unifier of $\exists \overline{\mathrm{X}} . C(\mathbf{1})$, and $f t v(\Gamma, \mathrm{T}) \subseteq \operatorname{dom}(\theta)$ (2) holds. The
rule's premises are $C, \Gamma \vdash \mathrm{t}: \mathrm{T}(\mathbf{3})$ and $\overline{\mathrm{X}} \# f t v(\Gamma, \mathrm{T})$. We may assume, w.l.o.g., $\overline{\mathrm{x}} \# \theta$ (4). As in the previous case, we may extend the domain of $\theta$ to guarantee $\operatorname{ftv}(\exists \overline{\mathrm{X}} . C) \subseteq \operatorname{dom}(\theta)$ (5). By (1), (4), (5), and Lemma 1.3.45, there exists a type substitution $\theta^{\prime}$ such that $\theta^{\prime}$ extends $\theta$ (6) and $\theta^{\prime}$ is a most general unifier of $C$. Applying the induction hypothesis to $\theta^{\prime}$ and to (3) yields $\llbracket \Gamma \rrbracket_{\theta^{\prime}} \vdash \mathrm{t}: \theta^{\prime}(\mathrm{T})$. By (2), (6), and Lemma 1.4.11, this may be read $\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{t}: \theta(\mathrm{T})$.

Together, Theorems 1.4.7 and 1.4.13 yield a precise correspondence between $\mathrm{DM}$ and $\operatorname{HM}(=)$ : there exists a compositional translation from each to the other. In other words, they may be viewed as two equivalent formulations of a single type system. One might also say that $\mathrm{HM}(=)$ is a constraint-based formulation of DM. Furthermore, Theorem 1.4.7 states that every member of the $\operatorname{HM}(X)$ family is an extension of DM. This explains our double interest in $\mathrm{HM}(X)$, as an alternate formulation of $\mathrm{DM}$, which we believe is more pleasant, for reasons already discussed, and as a more expressive framework.

\subsection*{1.5 A purely constraint-based type system: $\operatorname{PCB}(X)$}

In the previous section, we have presented $\operatorname{HM}(X)$, an elegant constraintbased extension of Damas and Milner's type system. However, $\operatorname{HM}(X)$, as described there, suffers from a drawback. A typing judgement involves both a constraint, which represents an assumption about its free type variables, and an environment, which represents an assumption about its free program identifiers. At a let node, HMD-LETGEN turns a part of the current constraint, namely $D$, into a type scheme, namely $\forall \overline{\mathrm{x}}[D] . \mathrm{T}$, and stores it into the environment. Then, at every occurrence of the let-bound variable, HMD-VARINST retrieves this type scheme from the environment and adds a copy of $D$ back to the current constraint. In practice, it is important to simplify the type scheme $\forall \overline{\mathrm{X}}[D] . \mathrm{T}$ before it is stored in the environment, because it would be inefficient to copy an unsimplified constraint. In other words, it appears that, in order to preserve efficiency, constraint generation and constraint simplification cannot be separated.

Of course, in practice, it is not difficult to intermix these phases, so the problem is not technical, but pedagogical. Indeed, we argued earlier that it is natural and desirable to separate them. Type scheme introduction and elimination constraints, which we introduced in Section 1.3 but did not use in the specification of $\operatorname{HM}(X)$, are intended as a means of solving this problem. In the present section, we exploit them to give a novel formulation of $\mathrm{HM}(X)$, which no longer requires copying constraints back and forth between the environment and the constraint assumption. In fact, the environment is

\begin{tabular}{cc|cc}
\hline$\frac{C \Vdash \mathrm{x} \preceq \mathrm{T}}{C \vdash \mathrm{x}: \mathrm{T}}$ & $(\mathrm{VAR})$ & $\frac{C_{1} \vdash \mathrm{t}_{1}: \mathrm{T}_{1} \quad C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}_{2}}{\text { let } \mathrm{z}: \forall \mathcal{V}\left[C_{1}\right] \cdot \mathrm{T}_{1} \text { in } C_{2}}$ & (LET) \\
$\frac{C \vdash \mathrm{t}: \mathrm{T}^{\prime}}{}$ & & \\
$\frac{\text { let } \mathrm{z}=\mathrm{t}_{1} \text { in } \mathrm{t}_{2}: \mathrm{T}_{2}}{}$ & \\
$\frac{C_{1} \vdash \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime} \quad C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}}{C_{1} \wedge C_{2} \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}}$ & $(\mathrm{APP})$ & $\frac{C \vdash \mathrm{t}: \mathrm{T}}{C \wedge \mathrm{T} \leq \mathrm{T}^{\prime} \vdash \mathrm{t}: \mathrm{T}^{\prime}}$ & (SUB) \\
& & $\frac{C \vdash \mathrm{t}: \mathrm{T} \quad \overline{\mathrm{x}} \# f t v(\mathrm{~T})}{\exists \overline{\mathrm{x}} \cdot C \vdash \mathrm{t}: \mathrm{T}}$ & (ExISTS) \\
\hline
\end{tabular}

Figure 1-9: Typing rules for $\operatorname{PCB}(X)$

suppressed altogether: taking advantage of the new constraint forms, we encode information about program identifiers within the constraint assumption.

\section*{Presentation}

We now employ the full constraint language (Section 1.3). Typing judgements take the form $C \vdash \mathrm{t}$ : $\mathrm{T}$, where $C$ may have free type variables and free program identifiers. The rules that allow deriving such judgements appear in Figure 1-9. As before, we identify judgements up to constraint equivalence.

Let us review the rules. VAR states that $\mathrm{x}$ has type $\mathrm{T}$ under any constraint that entails $\mathrm{x} \preceq \mathrm{T}$. Note that we no longer consult the type scheme associated with $\mathrm{x}$ in the environment-indeed, there is no environment. Instead, we let the constraint assumption record the fact that the type scheme should admit $\mathrm{T}$ as one of its instances. Thus, in a judgement $C \vdash \mathrm{t}: \mathrm{T}$, any program identifier that occurs free within $t$ typically also occurs free within $C$. ABs requires the body $\mathrm{t}$ of a $\lambda$-abstraction to have type $\mathrm{T}^{\prime}$ under assumption $C$. Although no explicit assumption about $\mathrm{z}$ appears in the premise, $C$ typically contains a number of instantiation constraints bearing on $z$, of the form $z \preceq T_{i}$. In the rule's conclusion, $C$ is wrapped within the prefix let $\mathrm{z}: \mathrm{T}$ in $[$, where $\mathrm{T}$ is the type assigned to $z$. This effectively requires every $T_{i}$ to denote a supertype of $\mathrm{T}$, as desired. Please note that $\mathbf{z}$ does not occur free in the constraint let $\mathrm{z}: \mathrm{T}$ in $C$, which is natural, since it does not occur free in $\lambda$ z.t. App exhibits a minor stylistic difference with respect to HMX-APP: its constraint assumption is split between its premises. It is not difficult to prove that, when weakening holds (see Lemma 1.5.2 below), this choice does not affect the set of valid judgements. This new presentation encourages reading the rules in Figure 1-9 as the specification of an algorithm, which, given $t$ and $T$, pro-
duces $C$ such that $C \vdash \mathrm{t}: \mathrm{T}$ holds. In the case of App, the algorithm invokes itself recursively for each of the two subexpressions, yielding the constraints $C_{1}$ and $C_{2}$, then constructs their conjunction. LET is analogous to ABS: by wrapping $C_{2}$ within a let prefix, it gives meaning to the instantiation constraints bearing on $\mathrm{z}$ within $C_{2}$. The difference is that $\mathrm{z}$ may now be assigned a type scheme, as opposed to a monotype. An appropriate type scheme is built in the most straightforward manner from the constraint $C_{1}$ and the type $\mathrm{T}_{1}$ that describe $t_{1}$. All of the type variables that appear free in the left-hand premise are generalized, hence the notation $\forall \mathcal{V}\left[C_{1}\right] . \mathrm{T}_{1}$, which is a convenient shorthand for $\forall \operatorname{ftv}\left(C_{1}, \mathrm{~T}_{1}\right)\left[C_{1}\right] . \mathrm{T}_{1}$. The side-condition that "type variables that occur free in the environment must not be generalized", which was present in $\mathrm{DM}$ and $\operatorname{HM}(X)$, naturally disappears, since judgements no longer involve an environment. SUB again exhibits a minor stylistic difference with respect to HMX-SUB: the comments made about APp above apply here as well. ExISTS is essentially identical to HMX-EXISTS.

In the standard specification of $\operatorname{HM}(X)$, HMD-ABS and HMD-LET GEN accumulate information in the environment. Through the environment, this information is made available to HMD-VARINST, which retrieves and copies it. Here, instead, no information is explicitly transmitted. Where a program identifier is bound, a type scheme introduction constraint is built; where a program identifier is used, a type scheme instantiation constraint is produced. The two are related only by our definition of the meaning of constraints.

The reader may be puzzled by the fact that LET allows all type variables that occur free in its left-hand premise to be generalized. The following exercise sheds some light on this issue.

1.5.1 Exercise [ $\star$, Recommended]: Build a type derivation for the expression $\lambda z_{1}$. let $z_{2}=z_{1}$ in $z_{2}$ within $\operatorname{PCB}(X)$. Draw a comparison with the solution of Exercise 1.2.21.

The following lemma is an analogue of Lemma 1.4.2.

1.5.2 Lemma [Weakening]: If $C^{\prime} \Vdash C$, then every derivation of $C \vdash \mathrm{t}: \mathrm{T}$ may be turned into a derivation of $C^{\prime} \vdash \mathrm{t}: \mathrm{T}$ with the same shape.

Proof: The proof is by structural induction on a derivation of $C \vdash t: T$. In each proof case, we adopt the notations of Figure 1-9.
- Case VAR. By transitivity of entailment.
- Case ABs. The rule's conclusion is let $\mathrm{z}: \mathrm{T}$ in $C \vdash \lambda$ z.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime}(\mathbf{1})$. By hypothesis, we have $C^{\prime} \Vdash$ let $\mathrm{z}: \mathrm{T}$ in $C$ (2). We may assume, w.l.o.g., $\mathrm{z} \notin f p i\left(C^{\prime}\right)(\mathbf{3})$. The rule's premise is $C \vdash \mathrm{t}: \mathrm{T}^{\prime}(\mathbf{4})$. Applying the induction hypothesis to (4) yields $C \wedge C^{\prime} \vdash \mathrm{t}: \mathrm{T}^{\prime}$, which by ABs implies let $\mathrm{z}: \mathrm{T}$ in $(C \wedge$
$\left.C^{\prime}\right) \vdash \lambda$ z.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime} \mathbf{( 5 )}$. By (3) and C-INAND*, let $\mathrm{z}: \mathrm{T}$ in $\left(C \wedge C^{\prime}\right)$ is equivalent to (let $\mathrm{z}: \mathrm{T}$ in $C$ ) $\wedge C^{\prime}$, which by (2) and $\mathrm{C}$-Dup is equivalent to $C^{\prime}$. Thus, (5) is the goal $C^{\prime} \vdash \lambda z$.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$.
- Case APp. By applying the induction hypothesis to each premise, using the fact that $C^{\prime} \Vdash C_{1} \wedge C_{2}$ implies $C^{\prime} \Vdash C_{1}$ and $C^{\prime} \Vdash C_{2}$.
- Case LET. Analogous to the case of ABS. The induction hypothesis is applied to the second premise only.
- Case Sub. Analogous to the case of Apr.
- Case ExISTs. See the corresponding case in the proof of Lemma 1.4.2.

\section*{Relating $\operatorname{PCB}(X)$ with $\operatorname{HM}(X)$}

Let us now provide evidence for our claim that $\operatorname{PCB}(X)$ is an alternate presentation of $\operatorname{HM}(X)$. The next two theorems define an effective translation from $\operatorname{HM}(X)$ to $\operatorname{PCB}(X)$ and back.

The first theorem states that if, within $\operatorname{HM}(X)$, $\mathrm{t}$ has type $\mathrm{T}$ under assumptions $C$ and $\Gamma$, then, within $\operatorname{PCB}(X)$, $\mathrm{t}$ also has type $\mathrm{T}$, under some assumption $C^{\prime}$. The relationship $C \Vdash$ let $\Gamma$ in $C^{\prime}$ states that $C$ entails the residual constraint obtained by confronting $\Gamma$, which provides information about the free program identifiers in $t$, with $C^{\prime}$, which contains instantiation constraints bearing on these program identifiers. The statement requires $C$ and $\Gamma$ to have no free program identifiers, which is natural, since they are part of an $\operatorname{HM}(X)$ judgement. The hypothesis $C \Vdash \exists \Gamma$ excludes the somewhat pathological situation where $\Gamma$ contains constraints not apparent in $C$. This hypothesis vanishes when $\Gamma$ is the initial environment; see Definition 1.7.3.

1.5.3 Theorem: Let $C \Vdash \exists \Gamma$. Assume $f p i(C, \Gamma)=\varnothing$. If $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ holds in $\operatorname{HM}(X)$, then there exists a constraint $C^{\prime}$ such that $C^{\prime} \vdash \mathrm{t}: \mathrm{T}$ holds in $\operatorname{PCB}(X)$ and $C$ entails let $\Gamma$ in $C^{\prime}$.

Proof: The proof is by structural induction on a derivation of $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$. In each proof case, we adopt the notations of Figure 1-8.
- Case HmD-VarInst. The rule's conclusion is $C \wedge D, \Gamma \vdash \mathrm{x}: \mathrm{T}$. By hypothesis, we have $C \wedge D \Vdash \exists \Gamma$ (1) and $f p i(C, D, \Gamma)=\varnothing$ (2). The rule's premise is $\Gamma(\mathrm{x})=\forall \overline{\mathrm{x}}[D] . \mathrm{T}$ (3). By VAR, we have $\mathrm{x} \preceq \mathrm{T} \vdash \mathrm{x}: \mathrm{T}$, so there remains to establish $C \wedge D \Vdash$ let $\Gamma$ in $\mathrm{x} \preceq \mathrm{T}$ (4). By (3), (2), and C-INID, the constraint let $\Gamma$ in $\mathrm{x} \preceq \mathrm{T}$ is equivalent to let $\Gamma$ in $\forall \overline{\mathrm{x}}[D]$. $\mathrm{T} \preceq \mathrm{T}$, which, by (2) and C-IN*, is itself equivalent to $\exists \Gamma \wedge \forall \overline{\mathrm{x}}[D] . \mathrm{T} \preceq \mathrm{T}$ (5). By (1) and Lemma 1.3.19, $C \wedge D$ entails (5). We have established (4).
- Case HmD-ABs. The rule's conclusion is $C, \Gamma \vdash \lambda z . \mathrm{t}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$. Its premise is $C,(\Gamma ; \mathbf{z}: \mathrm{T}) \vdash \mathrm{t}: \mathrm{T}^{\prime}(\mathbf{1})$. The constraints $\exists \Gamma$ and $\exists(\Gamma ; \mathbf{z}: \mathrm{T})$ are equivalent,
so the induction hypothesis applies to (1) and yields a constraint $C^{\prime}$ such that $C^{\prime} \vdash \mathrm{t}: \mathrm{T}^{\prime}(\mathbf{2})$ and $C \Vdash$ let $\Gamma ; \mathrm{z}: \mathrm{T}$ in $C^{\prime}$ (3). Applying ABs to (2) yields let $\mathrm{z}: \mathrm{T}$ in $C^{\prime} \vdash \lambda$ z.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$. There remains to check that $C$ entails let $\Gamma$ in let $\mathrm{z}: \mathrm{T}$ in $C^{\prime}$ —but that is precisely (3).
- Case HMD-App. The rule's conclusion is $C, \Gamma \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}$. Its premises are $C, \Gamma \vdash \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}(\mathbf{1})$ and $C, \Gamma \vdash \mathrm{t}_{2}: \mathrm{T}$ (2). Applying the induction hypothesis to (1) and (2), we obtain constraints $C_{1}^{\prime}$ and $C_{2}^{\prime}$ such that $C_{1}^{\prime} \vdash$ $\mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}(\mathbf{3})$ and $C_{2}^{\prime} \vdash \mathrm{t}_{2}: \mathrm{T}(4)$ and $C \Vdash$ let $\Gamma$ in $C_{1}^{\prime}(\mathbf{5})$ and $C \Vdash$ let $\Gamma$ in $C_{2}^{\prime}(\mathbf{6})$. By App, (3) and (4) imply $C_{1}^{\prime} \wedge C_{2}^{\prime} \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}$. Furthermore, by C-InAnd, (5) and (6) yield $C \Vdash$ let $\Gamma$ in $C_{1}^{\prime} \wedge C_{2}^{\prime}$.
- Case hmd-LetGen. The rule's conclusion is $C \wedge \exists \overline{\mathrm{x}} . D, \Gamma \vdash$ let $\mathrm{z}=$ $\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}_{2}$. By hypothesis, we have $C \wedge \exists \overline{\mathrm{x}} . D \Vdash \exists \Gamma(\mathbf{1})$ and $f p i(C, D, \Gamma)=$ $\varnothing$ (2). The rule's premises are $C \wedge D, \Gamma \vdash \mathrm{t}_{1}: \mathrm{T}_{1}$ (3) and $\overline{\mathrm{x}} \# f t v(C, \Gamma)$ (4) and $C \wedge \exists \overline{\mathrm{X}} . D, \Gamma^{\prime} \vdash \mathrm{t}_{2}: \mathrm{T}_{2}$ (5), where $\Gamma^{\prime}$ is $\Gamma ; \mathrm{z}: \forall \overline{\mathrm{x}}[D] . \mathrm{T}_{1}$. Applying the induction hypothesis to (3) yields a constraint $C_{1}^{\prime}$ such that $C_{1}^{\prime} \vdash \mathrm{t}_{1}: \mathrm{T}_{1}$ (6) and $C \wedge D \Vdash$ let $\Gamma$ in $C_{1}^{\prime}(\mathbf{7})$. By (1), (2), and C-IN*, we have $C \wedge \exists \overline{\mathrm{x}} . D \Vdash \exists \Gamma^{\prime}$. Thus, the induction hypothesis applies to (5) and yields a constraint $C_{2}^{\prime}$ such that $C_{2}^{\prime} \vdash \mathrm{t}_{2}: \mathrm{T}_{2}$ (8) and $C \wedge \exists \overline{\mathrm{x}}$. $D \Vdash$ let $\Gamma^{\prime}$ in $C_{2}^{\prime}$ (9). By LET, (6) and (8) imply let $\mathrm{z}: \forall \mathcal{V}\left[C_{1}^{\prime}\right] \cdot \mathrm{T}_{1}$ in $C_{2}^{\prime} \vdash$ let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}_{2}$ (10). By Lemmas 1.3 .25 and 1.5.2, (10) yields let $\mathrm{z}: \forall \overline{\mathrm{x}}\left[C_{1}^{\prime}\right] \cdot \mathrm{T}_{1}$ in $C_{2}^{\prime} \vdash$ let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}_{2}$ (11), where the universal quantification is over $\overline{\mathrm{X}}$ only. There remains to establish that $C \wedge \exists \overline{\mathrm{x}} . D$ entails let $\Gamma ; \mathrm{z}: \forall \overline{\mathrm{x}}\left[C_{1}^{\prime}\right] . \mathrm{T}_{1}$ in $C_{2}^{\prime}$ (12). By (4), (2), and CLETDup, the constraint (12) is equivalent to let $\Gamma ; \mathbf{z}: \forall \overline{\mathrm{X}}\left[\right.$ let $\Gamma$ in $\left.C_{1}^{\prime}\right] . \mathrm{T}_{1}$ in $C_{2}^{\prime}$. By (7), this constraint is entailed by let $\Gamma ; \mathrm{z}: \forall \overline{\mathrm{x}}[C \wedge D] . \mathrm{T}_{1}$ in $C_{2}^{\prime}$, which by (4) and C-LetAnd, is equivalent to $C \wedge$ let $\Gamma ; \mathbf{z}: \forall \overline{\mathrm{x}}[D] . \mathrm{T}_{1}$ in $C_{2}^{\prime}$, that is, $C \wedge$ let $\Gamma^{\prime}$ in $C_{2}^{\prime}$. By (9), this constraint is entailed by $C \wedge \exists \overline{\mathrm{x}}$. $D$.
- Case HmD-Sub. The rule's conclusion is $C, \Gamma \vdash \mathrm{t}: \mathrm{T}^{\prime}$. Its premises are $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (1) and $C \Vdash \mathrm{T} \leq \mathrm{T}^{\prime} \mathbf{( 2 )}$. Applying the induction hypothesis to (1) yields a constraint $C^{\prime}$ such that $C^{\prime} \vdash \mathrm{t}: \mathrm{T}$ (3) and $C \Vdash$ let $\Gamma$ in $C^{\prime}$ (4). By Sub, (3) implies $C^{\prime} \wedge \mathrm{T} \leq \mathrm{T}^{\prime} \vdash \mathrm{t}: \mathrm{T}^{\prime}$. There remains to establish $C \Vdash$ let $\Gamma$ in $\left(C^{\prime} \wedge \mathrm{T} \leq \mathrm{T}^{\prime}\right)$, which follows from (4) and (2) by C-InAnd*.

$\circ$ Case HmD-Exists. The rule's conclusion is $\exists \overline{\mathrm{x}} . C, \Gamma \vdash \mathrm{t}: \mathrm{T}$. Its premises are $C, \Gamma \vdash \mathrm{t}: \mathrm{T}(\mathbf{1})$ and $\overline{\mathrm{x}} \# f t v(\Gamma, \mathrm{T})(\mathbf{2})$. By hypothesis, we have $\exists \overline{\mathrm{x}} . C \Vdash$ $\exists \Gamma$, which by Lemma 1.3.16 implies $C \Vdash \exists \Gamma$. Thus, the induction hypothesis applies to (1) and yields a constraint $C^{\prime}$ such that $C^{\prime} \vdash \mathrm{t}: \mathrm{T}$ (3) and $C \Vdash$ let $\Gamma$ in $C^{\prime}$ (4). By Exists, (3) and (2) imply $\exists \overline{\mathrm{x}} . C^{\prime} \vdash \mathrm{t}$ : T. There remains to establish $\exists \overline{\mathrm{X}} . C \Vdash$ let $\Gamma$ in $\exists \overline{\mathrm{x}} . C^{\prime}$. By congruence of entailment, (4) implies $\exists \overline{\mathrm{X}} . C \Vdash \exists \overline{\mathrm{X}}$.let $\Gamma$ in $C^{\prime}$. The result follows by (2) and C-InEx.

The second theorem states that if, within $\operatorname{PCB}(X), \mathrm{t}$ has type $\mathrm{T}$ under assumption $C$, then, within $\operatorname{HM}(X)$, $\mathrm{t}$ also has type $\mathrm{T}$, under assumptions
let $\Gamma$ in $C$ and $\Gamma$. The idea is simple: the constraint $C$ represents a combined assumption about the initial judgement's free type variables and free program identifiers. In $\operatorname{HM}(X)$, these two kinds of assumptions must be maintained separately. So, we split them into a pair of an environment $\Gamma$, which may be chosen arbitrarily, provided it satisfies $f p i(C) \subseteq d p i(\Gamma)$-that is, provided it defines all program variables of interest, and the residual constraint let $\Gamma$ in $C$, which has no free program identifiers, thus represents an assumption about the new judgement's type variables only. Distinct choices of $\Gamma$ give rise to distinct $\operatorname{HM}(X)$ judgements, which may be incomparable; this is related to the fact that ML-the-type-system does not have principal typings (Jim, 1995). Again, the hypothesis $f p i(\Gamma)=f p i($ let $\Gamma$ in $C)=\varnothing$ is natural, since we wish $\Gamma$ and let $\Gamma$ in $C$ to appear in an $\operatorname{HM}(X)$ judgement.

1.5.4 Theorem: Assume $f p i(\Gamma)=f p i($ let $\Gamma$ in $C)=\varnothing$ and $C \not \equiv$ false. If $C \vdash \mathrm{t}: \mathrm{T}$ holds in $\operatorname{PCB}(X)$, then let $\Gamma$ in $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ holds in $\operatorname{HM}(X)$.

Proof: The proof is by structural induction on a derivation of $C \vdash \mathrm{t}: \mathrm{T}$. In each proof case, we adopt the notations of Figure 1-9.

By Lemma 1.3.30, the hypothesis $C \not \equiv$ false is preserved whenever the induction hypothesis is invoked. It is explicitly used only in case VAR, where it guarantees that the identifier at hand is bound in $\Gamma$.
- Case VAR. The rule's conclusion is $C \vdash \mathrm{x}$ : T. Its premise is $C \Vdash \mathrm{x} \preceq$ T (1). By Lemma 1.3.24, (1) and the hypothesis $C \not \equiv$ false imply $\mathrm{x} \in f p i(C)$. Because let $\Gamma$ in $C$ has no free program identifiers, this implies $\mathrm{x} \in d p i(\Gamma)$, that is, the environment $\Gamma$ must define $\mathrm{x}$. Let $\Gamma(\mathrm{x})=\forall \overline{\mathrm{x}}[D] \cdot \mathrm{T}^{\prime}$ (2), where $\overline{\mathrm{X}} \# \operatorname{ftv}(\Gamma, \mathrm{T})$ (3). By (2), HMD-VARInst, and HMD-SuB, we have $D \wedge \mathrm{T}^{\prime} \leq$ $\mathrm{T}, \Gamma \vdash \mathrm{x}: \mathrm{T}$. By (3) and HMD-ExisTs, this implies $\exists \overline{\mathrm{X}} .\left(D \wedge \mathrm{T}^{\prime} \leq \mathrm{T}\right), \Gamma \vdash \mathrm{x}: \mathrm{T}$ (4). Now, by (3), the constraint $\exists \overline{\mathrm{X}} .\left(D \wedge \mathrm{T}^{\prime} \leq \mathrm{T}\right)$ may be written $\forall \overline{\mathrm{X}}[D] . \mathrm{T}^{\prime} \preceq \mathrm{T}$ (5). The hypothesis $f p i(\Gamma)=\varnothing$ implies $f p i(D)=\varnothing$ (6). By (6), C-InID and C$\mathrm{IN}^{*},(5)$ is equivalent to let $\Gamma$ in $\mathrm{x} \preceq \mathrm{T}$. Thus, (4) may be written let $\Gamma$ in $\mathrm{x} \preceq$ $\mathrm{T}, \Gamma \vdash \mathrm{x}: \mathrm{T}$. By (1), by congruence of entailment, and by Lemma 1.4.2, this implies let $\Gamma$ in $C, \Gamma \vdash \mathrm{x}: \mathrm{T}$.
- Case ABs. The rule's conclusion is let z : $\mathrm{T}$ in $C \vdash \lambda$ z.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$. Its premise is $C \vdash \mathrm{t}: \mathrm{T}^{\prime} \mathbf{( 1 )}$. Let $\Gamma^{\prime}$ stand for $\Gamma ; \mathrm{z}: \mathrm{T}$. Applying the induction hypothesis to (1) yields let $\Gamma^{\prime}$ in $C, \Gamma^{\prime} \vdash \mathrm{t}: \mathrm{T}^{\prime}$. By HMD-ABS, this implies let $\Gamma^{\prime}$ in $C, \Gamma \vdash \lambda z$.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$.
- Case App. The rule's conclusion is $C_{1} \wedge C_{2} \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}$. Its premises are $C_{1} \vdash \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$ and $C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}$. Applying the induction hypothesis yields respectively let $\Gamma$ in $C_{1}, \Gamma \vdash \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$ and let $\Gamma$ in $C_{2}, \Gamma \vdash \mathrm{t}_{2}: \mathrm{T}$, which by Lemma 1.4.2 and HMD-APP imply let $\Gamma$ in $\left(C_{1} \wedge C_{2}\right), \Gamma \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}$.

$\circ$ Case LET. The rule's conclusion is let $\mathrm{z}: \forall \mathcal{V}\left[C_{1}\right] \cdot \mathrm{T}_{1}$ in $C_{2} \vdash$ let $\mathrm{z}=$
$\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}_{2}$. Its premises are $C_{1} \vdash \mathrm{t}_{1}: \mathrm{T}_{1} \mathbf{( 1 )}$ and $C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}_{2} \mathbf{( 2 )}$. Let $\overline{\mathrm{X}}$ stand for $f t v\left(C_{1}, \mathrm{~T}_{1}\right)$. We may require, w.l.o.g., $\overline{\mathrm{X}} \# f t v\left(\Gamma, C_{2}\right)$ (3). By hypothesis, we have $f p i(\Gamma)=\varnothing(4)$. We also have $f p i\left(\right.$ let $\Gamma ; \mathbf{z}: \forall \mathcal{V}\left[C_{1}\right] . \mathrm{T}_{1}$ in $\left.C_{2}\right)=\varnothing$, which implies $f p i\left(\right.$ let $\Gamma$ in $\left.C_{1}\right)=\varnothing$. Thus, the induction hypothesis applies to (1) and yields let $\Gamma$ in $C_{1}, \Gamma \vdash \mathrm{t}_{1}: \mathrm{T}_{1}$ (5). Now, let $\sigma$ stand for $\forall \overline{\mathrm{X}}\left[\right.$ let $\Gamma$ in $\left.C_{1}\right] . \mathrm{T}_{1}$ and $\Gamma^{\prime}$ stand for $\Gamma ; \mathbf{z}: \sigma$. We have $f p i\left(\Gamma^{\prime}\right)=$ $f p i\left(\right.$ let $\Gamma^{\prime}$ in $\left.C_{2}\right)=\varnothing$. Thus, the induction hypothesis applies to (2) and yields let $\Gamma^{\prime}$ in $C_{2}, \Gamma^{\prime} \vdash \mathrm{t}_{2}: \mathrm{T}_{2}$ (6). Let us now weaken (5) and (6) so as to make them suitable premises for HMD-LETGEN. Applying Lemma 1.4.2 to (5) yields (let $\Gamma^{\prime}$ in $C_{2}$ ) $\wedge\left(\right.$ let $\Gamma$ in $C_{1}$ ), $\Gamma \vdash \mathrm{t}_{1}: \mathrm{T}_{1}$ (7). Applying Lemma 1.4.2 to (6) yields (let $\Gamma^{\prime}$ in $C_{2}$ ) $\neg \exists \overline{\mathrm{X}}$. (let $\Gamma$ in $C_{1}$ ), $\Gamma^{\prime} \vdash \mathrm{t}_{2}: \mathrm{T}_{2}$ (8). Last, (3) implies $\overline{\mathrm{X}} \# f t v\left(\Gamma\right.$, let $\Gamma^{\prime}$ in $C_{2}$ ) (9). Applying Hmd-LetGen to (7), (9) and (8), we obtain (let $\Gamma^{\prime}$ in $\left.C_{2}\right) \wedge \exists \overline{\mathrm{x}}$. (let $\Gamma$ in $C_{1}$ ), $\Gamma \vdash$ let z $=\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}_{2}$ (10). Now, by (4), (3), and C-LetDup, let $\Gamma^{\prime}$ in $C_{2}$ is equivalent to let $\Gamma ; \mathbf{z}: \forall \overline{\mathrm{X}}\left[C_{1}\right] . \mathrm{T}_{1}$ in $C_{2}$. Using this fact, as well as (3), C-InEx, and C-InAnd, we find that the constraint (let $\Gamma^{\prime}$ in $C_{2}$ ) $\neg \exists \overline{\mathrm{x}}$. (let $\Gamma$ in $C_{1}$ ) is equivalent to let $\Gamma$ in (let $\mathrm{z}$ : $\forall \overline{\mathrm{X}}\left[C_{1}\right] . \mathrm{T}_{1}$ in $C_{2} \wedge \exists \overline{\mathrm{x}} . C_{1}$ ), which by definition of the let form, is itself equivalent to let $\Gamma ; z: \forall \overline{\mathrm{X}}\left[C_{1}\right] . \mathrm{T}_{1}$ in $C_{2}$. Last, by definition of $\overline{\mathrm{X}}$, this constraint is let $\Gamma ; \mathbf{z}: \forall \mathcal{V}\left[C_{1}\right]$. $\mathrm{T}_{1}$ in $C_{2}$. Thus, (10) is the goal.
- Case Sub. The rule's conclusion is $C \wedge \mathrm{T} \leq \mathrm{T}^{\prime} \vdash \mathrm{t}: \mathrm{T}^{\prime}$. Its premise is $C \vdash \mathrm{t}$ : $\mathrm{T}$ (1). Applying the induction hypothesis to (1) yields let $\Gamma$ in $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (2). By Lemma 1.4.2 and HMD-Sub, (2) implies (let $\Gamma$ in $C$ ) $\wedge \mathrm{T} \leq \mathrm{T}^{\prime}, \Gamma \vdash \mathrm{t}: \mathrm{T}^{\prime}$, which by C-InAnd* may be written let $\Gamma$ in $\left(C \wedge \mathrm{T} \leq \mathrm{T}^{\prime}\right), \Gamma \vdash \mathrm{t}: \mathrm{T}^{\prime}$.

$\circ$ Case ExIsTs. The rule's conclusion is $\exists \overline{\mathrm{x}} . C \vdash \mathrm{t}$ : T. Its premises are $C \vdash$ $\mathrm{t}: \mathrm{T}$ (1) and $\overline{\mathrm{X}} \# \mathrm{ftv}(\mathrm{T})$ (2). We may further require, w.l.o.g., $\overline{\mathrm{X}} \# \mathrm{ftv}(\Gamma)$ (3). Applying the induction hypothesis to (1) yields let $\Gamma$ in $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (4). Applying HmD-Exists to (2), (3), and (4), we find $\exists \overline{\mathrm{X}}$.let $\Gamma$ in $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$, which, by (3) and C-INEx, may be written let $\Gamma$ in $\exists \overline{\mathrm{x}} . C, \Gamma \vdash \mathrm{t}: \mathrm{T}$.

As a corollary, we find that, for closed programs, the type systems $\operatorname{HM}(X)$ and $\operatorname{PCB}(X)$ coincide. In particular, a program is well-typed with respect to one if and only if it is well-typed with respect to the other. This supports the view that $\operatorname{PCB}(X)$ is an alternate formulation of $\operatorname{HM}(X)$.

1.5.5 Theorem: Assume $f p i(C)=\varnothing$ and $C \not \equiv$ false. Then, $C, \varnothing \vdash \mathrm{t}: \mathrm{T}$ holds in $\mathrm{HM}(X)$ if and only if $C \vdash \mathrm{t}: \mathrm{T}$ holds in $\operatorname{PCB}(X)$.

\subsection*{1.6 Constraint generation}

We now explain how to reduce type inference problems for $\operatorname{PCB}(X)$ to constraint solving problems. A type inference problem consists of an expression

$$
\begin{aligned}
\llbracket \mathrm{x}: \mathrm{T} \rrbracket & =\mathrm{x} \preceq \mathrm{T} \\
\llbracket \lambda \mathrm{z} \cdot \mathrm{t}: \mathrm{T} \rrbracket & =\exists \mathrm{x}_{1} \mathrm{X}_{2} \cdot\left(\text { let } \mathrm{z}: \mathrm{x}_{1} \text { in } \llbracket \mathrm{t}: \mathrm{x}_{2} \rrbracket \wedge \mathrm{X}_{1} \rightarrow \mathrm{x}_{2} \leq \mathrm{T}\right) \\
\llbracket \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T} \rrbracket & =\exists \mathrm{x}_{2} \cdot\left(\llbracket \mathrm{t}_{1}: \mathrm{x}_{2} \rightarrow \mathrm{T} \rrbracket \wedge \llbracket \mathrm{t}_{2}: \mathrm{x}_{2} \rrbracket\right) \\
\llbracket \text { let } \mathrm{z}=\mathrm{t}_{1} \text { in } \mathrm{t}_{2}: \mathrm{T} \rrbracket & =\text { let } \mathrm{z}: \forall \mathrm{x}\left[\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket\right] \cdot \mathrm{X} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket
\end{aligned}
$$

Figure 1-10: Constraint generation

$t$ and a type $T$ of kind $\star$. The problem is to determine whether $t$ is well-typed with type $\mathrm{T}$, that is, whether there exists a satisfiable constraint $C$ such that $C \vdash \mathrm{t}: \mathrm{T}$ holds. This formulation of the problem may seem to require an appropriate type $\mathrm{T}$ to be known in advance; this is not really the case, since $\mathrm{T}$ may be a type variable. A constraint solving problem consists of a constraint $C$. The problem is to determine whether $C$ is satisfiable. To reduce a type inference problem ( $\mathrm{t}, \mathrm{T})$ to a constraint solving problem, we must produce a constraint $C$ that is both sufficient and necessary for $C \vdash \mathrm{t}: \mathrm{T}$ to hold. Below, we explain how to compute such a constraint, which we write $\llbracket t: T \rrbracket$. We check that it is indeed sufficient by proving $\llbracket \mathrm{t}: \mathrm{T} \rrbracket \vdash \mathrm{t}: \mathrm{T}$. That is, the constraint $\llbracket t: T \rrbracket$ is specific enough to guarantee that $t$ has type $T$. We say that constraint generation is sound. We check that it is indeed necessary by proving that, for every constraint $C, C \vdash \mathrm{t}: \mathrm{T}$ implies $C \Vdash \llbracket \mathrm{t}: \mathrm{T} \rrbracket$. That is, every constraint that guarantees that $\mathrm{t}$ has type $\mathrm{T}$ is at least as specific as $\llbracket \mathrm{t}: \mathrm{T} \rrbracket$. We say that constraint generation is complete. Together, these properties mean that $\llbracket \mathrm{t}: \mathrm{T} \rrbracket$ is the least specific constraint that guarantees that $\mathrm{t}$ has type $\mathrm{T}$.

We now see how to reduce a type inference problem to a constraint solving problem. Indeed, if there exists a satisfiable constraint $C$ such that $C \vdash \mathrm{t}: \mathrm{T}$ holds, then, by the completeness property, $C \Vdash \llbracket t: \mathrm{T} \rrbracket$ holds, so $\llbracket \mathrm{t}: \mathrm{T} \rrbracket$ is satisfiable. Conversely, the soundness property states that $\llbracket \mathrm{t}: \mathrm{T} \rrbracket \vdash \mathrm{t}: \mathrm{T}$ holds, so, if $\llbracket \mathrm{t}: \mathrm{T} \rrbracket$ is satisfiable, then there exists a satisfiable constraint $C$ such that $C \vdash \mathrm{t}: \mathrm{T}$ holds. In other words, $\mathrm{t}$ is well-typed with type $\mathrm{T}$ if and only if $\llbracket t: T \rrbracket$ is satisfiable.

The existence of such a constraint is the analogue of the existence of principal type schemes in classic presentations of ML-the-type-system (Damas and Milner, 1982). Indeed, a principal type scheme is least specific in the sense that all valid types are substitution instances of it. Here, the constraint $\llbracket t: T \rrbracket$ is least specific in the sense that all valid constraints entail it. Earlier, we have established a connection between constraint entailment and refinement of type substitutions, in the specific case of equality constraints interpreted over a free algebra of finite types; see Lemma 1.3.39.

The constraint $\llbracket t: T \rrbracket$ is defined in Figure 1-10 by induction on the structure of the expression $t$. We refer to these defining equations as the constraint generation rules. The definition is quite terse. It is perhaps even simpler than the declarative specification of $\operatorname{PCB}(X)$ given in Figure 1-9; yet, we prove below that the two are equivalent.

Before explaining the definition, we state the requirements that bear on the type variables $\mathrm{X}_{1}, \mathrm{X}_{2}$, and $\mathrm{X}$, which appear bound in the right-hand sides of the second, third, and fourth equations. These type variables must have kind $\star$. They must be chosen distinct (that is, $\mathrm{X}_{1} \neq \mathrm{X}_{2}$ in the second equation) and fresh in the following sense: type variables that appear bound in an equation's right-hand side must not appear free in the equation's left-hand side. Provided this restriction is obeyed, different choices of $\mathrm{X}_{1}, \mathrm{X}_{2}$, and $\mathrm{X}$ lead to $\alpha$-equivalent constraints - that is, to the same constraint, since we identify objects up to $\alpha$-conversion - which guarantees that the above equations make sense. We remark that, since expressions do not have free type variables, the freshness requirement may be simplified to: type variables that appear bound in an equation's right-hand side must not appear free in T. However, this simplification is rendered invalid by the introduction of type annotations within expressions (page 102). Please note that we are able to state a formal freshness requirement. This is made possible by the fact that $\llbracket t: T \rrbracket$ has no free type variables other than those of $\mathrm{T}$, which in turn depends on our explicit use of existential quantification.

Let us now review the four equations. The first one simply mirrors VAR. The second one requires $t$ to have type $x_{2}$ under the hypothesis that $z$ has type $\mathrm{X}_{1}$, and forms the arrow type $\mathrm{X}_{1} \rightarrow \mathrm{X}_{2}$; this corresponds to ABs. Here, $\mathrm{X}_{1}$ and $X_{2}$ must be fresh type variables, because we cannot in general guess the expected types of $z$ and $t$. The expected type $\mathrm{T}$ is required to be a supertype of $\mathrm{X}_{1} \rightarrow \mathrm{X}_{2}$; this corresponds to SUB. We must bind the fresh type variables $\mathrm{X}_{1}$ and $\mathrm{X}_{2}$, so as to guarantee that the generated constraint is unique up to $\alpha$-conversion. Furthermore, we must bind them existentially, because we intend the constraint solver to choose some appropriate value for them. This is justified by Exists. The third equation uses the fresh type variable $\mathrm{X}_{2}$ to stand for the unknown type of $t_{2}$. The subexpression $t_{1}$ is expected to have type $\mathrm{X}_{2} \rightarrow \mathrm{T}$. This corresponds to APP. The fourth equation, which corresponds to LET, is most interesting. It summons a fresh type variable $\mathrm{X}$ and produces $\llbracket t_{1}: x \rrbracket$. This constraint, whose sole free type variable is $\mathrm{X}$, is the least specific constraint that must be imposed on $\mathrm{X}$ so as to make it a valid type for $\mathrm{t}_{1}$. As a result, the type scheme $\forall \mathrm{x}\left[\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket\right] . \mathrm{X}$, abbreviated $\sigma$ in the following, is a principal type scheme for $t_{1}$. There remains to place $\llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket$ inside the context let $\mathrm{z}: \sigma$ in $\square$. Indeed, when placed inside this context, an instantiation constraint of the form $\mathrm{z} \preceq \mathrm{T}^{\prime}$ acquires the meaning
$\sigma \preceq \mathrm{T}^{\prime}$, which by definition of $\sigma$ and by Lemma 1.6.4 (see below) is equivalent to $\llbracket t_{1}: T^{\prime} \rrbracket$. Thus, the constraint produced by the fourth equation simulates a textual expansion of the let construct, whereby every occurrence of $z$ would be replaced with $t_{1}$. Thanks to type scheme introduction and instantiation constraints, however, this effect is achieved without duplication of source code or constraints. In other words, constraint generation has linear time and space complexity; duplication may take place during constraint solving only.

1.6.1 EXERCISE $[\star, \nrightarrow]$ : Define the size of an expression, of a type, and of a constraint, viewed as abstract syntax trees. Check that the size of $\llbracket t: T \rrbracket$ is linear in the sum of the sizes of $t$ and $T$.

We now establish several properties of constraint generation. We begin with soundness, whose proof is straightforward.

1.6.2 Theorem [Soundness]: $\mathrm{t}: \mathrm{T} \rrbracket \vdash \mathrm{t}: \mathrm{T}$.

Proof: By induction on the structure of $t$.
- Case $\mathrm{x}$. The goal $\mathrm{x} \preceq \mathrm{T} \vdash \mathrm{x}: \mathrm{T}$ follows from VAR.
- Case $\lambda$ z.t. By the induction hypothesis, we have $\llbracket t: \mathrm{x}_{2} \rrbracket \vdash \mathrm{t}: \mathrm{x}_{2}$. By ABs, this implies let $\mathrm{z}: \mathrm{x}_{1}$ in $\llbracket \mathrm{t}: \mathrm{x}_{2} \rrbracket \vdash \lambda z$. $\mathrm{t}: \mathrm{x}_{1} \rightarrow \mathrm{X}_{2}$. By SuB, this implies let $\mathrm{z}: \mathrm{X}_{1}$ in $\llbracket \mathrm{t}: \mathrm{X}_{2} \rrbracket \wedge \mathrm{X}_{1} \rightarrow \mathrm{X}_{2} \leq \mathrm{T} \vdash \lambda \mathrm{z} . \mathrm{t}: \mathrm{T}$. Lastly, because $\mathrm{X}_{1} \mathrm{X}_{2} \# \operatorname{ftv}(\mathrm{T})$ holds, ExISTS applies and yields $\llbracket \lambda z . t: \mathrm{T} \rrbracket \vdash \lambda z . t: \mathrm{T}$.
- Case $\mathrm{t}_{1} \mathrm{t}_{2}$. By the induction hypothesis, we have $\llbracket \mathrm{t}_{1}: \mathrm{x}_{2} \rightarrow \mathrm{T} \rrbracket \vdash \mathrm{t}_{1}$ : $\mathrm{x}_{2} \rightarrow \mathrm{T}$ and $\llbracket \mathrm{t}_{2}: \mathrm{x}_{2} \rrbracket \vdash \mathrm{t}_{2}: \mathrm{x}_{2}$. By APP, this implies $\llbracket \mathrm{t}_{1}: \mathrm{x}_{2} \rightarrow \mathrm{T} \rrbracket \wedge$ $\llbracket \mathrm{t}_{2}: \mathrm{X}_{2} \rrbracket \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}$. Because $\mathrm{X}_{2} \notin f t v(\mathrm{~T})$ holds, ExISTs applies and yields $\llbracket \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T} \rrbracket \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}$.
- Case let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}$. By the induction hypothesis, we have $\llbracket \mathrm{t}_{1}$ : $\mathrm{x} \rrbracket \vdash \mathrm{t}_{1}: \mathrm{x}$ and $\llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket \vdash \mathrm{t}_{2}:$ T. By LET, these imply let $\mathrm{z}: \forall \mathcal{V}\left[\llbracket \mathrm{t}_{1}:\right.$ $\mathrm{x} \rrbracket] . \mathrm{X}$ in $\llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket \vdash$ let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}$. Because $\mathrm{ftv}\left(\llbracket \mathrm{t}_{1}: \mathrm{X} \rrbracket\right)$ is $\mathrm{X}$, the universal quantification on $\mathcal{V}$ really bears on $X$ alone. We have proved $\llbracket l$ et $z=t_{1}$ in $t_{2}$ : $\mathrm{T} \rrbracket \vdash$ let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}$.

The following lemmas are used in the proof of the completeness property and in a number of other occasions. The first two state that $\llbracket t: T \rrbracket$ is covariant with respect to $\mathrm{T}$. Roughly speaking, this means that enough subtyping constraints are generated to achieve completeness with respect to SUB.

1.6.3 Lemma: $\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{T}^{\prime}$ entails $\llbracket \mathrm{t}: \mathrm{T}^{\prime} \rrbracket$.

1.6.4 Lemma: $\mathrm{X} \notin f t v(\mathrm{~T})$ implies $\exists \mathrm{X} .(\llbracket \mathrm{t}: \mathrm{X} \rrbracket \wedge \mathrm{X} \leq \mathrm{T}) \equiv \llbracket \mathrm{t}: \mathrm{T} \rrbracket$.

The next lemma gives a simplified version of the second constraint generation rule, in the specific case where the expected type is an arrow type. Then, fresh type variables need not be generated; one may directly use the arrow's domain and codomain instead.

Lemma: $\llbracket \lambda$ z.t : $\mathrm{T}_{1} \rightarrow \mathrm{T}_{2} \rrbracket$ is equivalent to let $\mathrm{z}: \mathrm{T}_{1}$ in $\llbracket \mathrm{t}: \mathrm{T}_{2} \rrbracket$.

We conclude with the completeness property.

1.6.6 Theorem [Completeness]: if $C \vdash \mathrm{t}: \mathrm{T}$, then $C \Vdash \llbracket \mathrm{t}: \mathrm{T} \rrbracket$.

Proof: By induction on the derivation of $C \vdash \mathrm{t}: \mathrm{T}$.

๑ Case VAR. The rule's conclusion is $C \vdash \mathrm{x}$ : T. Its premise is $C \Vdash \mathrm{x} \preceq \mathrm{T}$, which is also the goal.
- Case ABs. The rule's conclusion is let z : $\mathrm{T}$ in $C \vdash \lambda z . t: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$. Its premise is $C \vdash \mathrm{t}: \mathrm{T}^{\prime}$. By the induction hypothesis, we have $C \Vdash \llbracket \mathrm{t}: \mathrm{T}^{\prime} \rrbracket$. By congruence of entailment, this implies let $\mathrm{z}: \mathrm{T}$ in $C \Vdash$ let $\mathrm{z}: \mathrm{T}$ in $\llbracket \mathrm{t}: \mathrm{T}^{\prime} \rrbracket$, which, by Lemma 1.6.5, may be written let $\mathrm{z}: \mathrm{T}$ in $C \Vdash \llbracket \lambda z . \mathrm{t}: \mathrm{T} \rightarrow \mathrm{T}^{\prime} \rrbracket$.
- Case App. The rule's conclusion is $C_{1} \wedge C_{2} \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}$. Its premises are $C_{1} \vdash \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$ and $C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}$. By the induction hypothesis, we have $C_{1} \Vdash$ $\llbracket \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime} \rrbracket$ and $C_{2} \Vdash \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket$. Thus, $C_{1} \wedge C_{2}$ entails $\llbracket \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime} \rrbracket \wedge \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket$, which, by C-NAMEEQ, may be written $\exists \mathrm{X}_{2} \cdot\left(\mathrm{X}_{2}=\mathrm{T} \wedge \llbracket \mathrm{t}_{1}: \mathrm{X}_{2} \rightarrow \mathrm{T}^{\prime} \rrbracket \wedge \llbracket \mathrm{t}_{2}: \mathrm{X}_{2} \rrbracket\right)$, where $\mathrm{X}_{2} \notin f t v\left(\mathrm{~T}, \mathrm{~T}^{\prime}\right)$. Forgetting about the equation $\mathrm{X}_{2}=\mathrm{T}$, we find that $C_{1} \wedge C_{2}$ entails $\exists \mathrm{X}_{2} \cdot\left(\llbracket \mathrm{t}_{1}: \mathrm{X}_{2} \rightarrow \mathrm{T}^{\prime} \rrbracket \wedge \llbracket \mathrm{t}_{2}: \mathrm{X}_{2} \rrbracket\right)$, which is precisely $\llbracket \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime} \rrbracket$.
- Case Let. The rule's conclusion is let $\mathrm{z}: \forall \mathcal{V}\left[C_{1}\right] . \mathrm{T}_{1}$ in $C_{2} \vdash$ let $\mathrm{z}=$ $\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}_{2}$. Its premises are $C_{1} \vdash \mathrm{t}_{1}: \mathrm{T}_{1}$ and $C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}_{2}$. By the induction hypothesis, we have $C_{1} \Vdash \llbracket \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket$ and $C_{2} \Vdash \llbracket \mathrm{t}_{2}: \mathrm{T}_{2} \rrbracket$, which implies let $\mathrm{z}: \forall \mathcal{V}\left[C_{1}\right] . \mathrm{T}_{1}$ in $C_{2} \Vdash$ let $\mathrm{z}: \forall \mathcal{V}\left[\llbracket \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket\right] . \mathrm{T}_{1}$ in $\llbracket \mathrm{t}_{2}: \mathrm{T}_{2} \rrbracket$ (1).

Now, let us establish true $\Vdash \forall \mathrm{x}\left[\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket\right] . \mathrm{x} \preceq \forall \mathcal{V}\left[\llbracket \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket\right] . \mathrm{T}_{1}$ (2). By definition, this requires proving $\exists \overline{\mathrm{X}}_{1} \cdot\left(\llbracket \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket \wedge \mathrm{T}_{1} \leq \mathrm{Z}\right) \Vdash \exists \mathrm{X} .\left(\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket \wedge \mathrm{X} \leq\right.$ Z) (3), where $\overline{\mathrm{X}}_{1}=f t v\left(\mathrm{~T}_{1}\right)$ and $\mathrm{Z} \notin \mathrm{X} \overline{\mathrm{X}}_{1}$ (4). By Lemma 1.6.3, (4), and CEx*, the left-hand side of (3) entails $\llbracket t_{1}: \mathrm{z} \rrbracket$. By (4) and Lemma 1.6.4, the right-hand side of (3) is $\llbracket t_{1}: z \rrbracket$. Thus, (3) holds, and so does (2).

By $(2)$ and Lemma 1.3.22, we have let $\mathrm{z}: \forall \mathcal{V}\left[\llbracket \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket\right] . \mathrm{T}_{1}$ in $\llbracket \mathrm{t}_{2}: \mathrm{T}_{2} \rrbracket \Vdash$ let $\mathrm{z}: \forall \mathrm{X}\left[\llbracket \mathrm{t}_{1}: \mathrm{X} \rrbracket\right] \cdot \mathrm{X}$ in $\llbracket \mathrm{t}_{2}: \mathrm{T}_{2} \rrbracket$ (5). By transitivity of entailment, (1) and (5) yield let $\mathrm{z}: \forall \mathcal{V}\left[C_{1}\right] . \mathrm{T}_{1}$ in $C_{2} \Vdash \llbracket$ let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}_{2} \rrbracket$.
- Case Sub. The rule's conclusion is $C \wedge \mathrm{T} \leq \mathrm{T}^{\prime} \vdash \mathrm{t}: \mathrm{T}^{\prime}$. Its premise is $C \vdash \mathrm{t}: \mathrm{T}$. By the induction hypothesis, we have $C \Vdash \llbracket \mathrm{t}: \mathrm{T} \rrbracket$, which implies $C \wedge \mathrm{T} \leq \mathrm{T}^{\prime} \Vdash \llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{T}^{\prime}$. By lemma 1.6.3 and by transitivity of entailment, we obtain $C \wedge \mathrm{T} \leq \mathrm{T}^{\prime} \Vdash \llbracket \mathrm{t}: \mathrm{T}^{\prime} \rrbracket$.

$\circ$ Case Exists. The rule's conclusion is $\exists \overline{\mathrm{x}} . C \vdash \mathrm{t}$ : $\mathrm{T}$. Its premises are $C \vdash \mathrm{t}: \mathrm{T}$ and $\overline{\mathrm{x}} \# f t v(\mathrm{~T})$ (1). By the induction hypothesis, we have $C \Vdash \llbracket \mathrm{t}: \mathrm{T} \rrbracket$.

By congruence of entailment, this implies $\exists \overline{\mathrm{X}} . C \Vdash \exists \overline{\mathrm{X}}$. $\mathrm{t}: \mathrm{T} \rrbracket$ (2). Furthermore, (1) implies $\overline{\mathrm{X}}$ \# ftv( $\llbracket \mathrm{t}: \mathrm{T} \rrbracket)$ (3). By (3) and C-Ex*, (2) may be written $\exists \overline{\mathrm{x}} . C \Vdash \llbracket \mathrm{t}: \mathrm{T} \rrbracket$.

\subsection*{1.7 Type soundness}

We are now ready to establish type soundness for our type system. The statement that we wish to prove is sometimes known as Milner's slogan: well-typed programs do not go wrong (Milner, 1978). Below, we define well-typedness in terms of our constraint generation rules, for the sake of convenience, and establish type soundness with respect to that particular definition. Theorems 1.4.7, 1.5.4, and 1.6.6 imply that type soundness also holds when well-typedness is defined with respect to the typing judgements of $\mathrm{DM}, \operatorname{HM}(X)$, or $\mathrm{PCB}(X)$. We establish type soundness by following Wright and Felleisen's so-called syntactic approach (1994b). The approach consists in isolating two independent properties. Subject reduction, whose exact statement will be given below, implies that well-typedness is preserved by reduction. Progress states that no stuck configuration is well-typed. It is immediate to check that, if both properties hold, then no well-typed program can reduce to a stuck configuration. Subject reduction itself depends on a key lemma, usually known as a (term) substitution lemma. We immediately give two versions of this lemma: the former is stated in terms of $\operatorname{PCB}(X)$ judgements, while the latter is stated in terms of the constraint generation rules.

1.7.1 Lemma [Substitution]: $C \vdash \mathrm{t}: \mathrm{T}$ and $C_{0} \vdash \mathrm{t}_{0}: \mathrm{T}_{0}$ imply let $\mathrm{z}_{0}$ : $\forall \overline{\mathrm{x}}_{0}\left[C_{0}\right] . \mathrm{T}_{0}$ in $C \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}: \mathrm{T}$.

Proof: The proof is by structural induction on the derivation of $C \vdash \mathrm{t}: \mathrm{T}$. In each proof case, we adopt the notations of Figure 1-9. We write $\sigma_{0}$ for $\forall \overline{\mathrm{x}}_{0}\left[C_{0}\right] . \mathrm{T}_{0}$. We refer to the hypothesis $C_{0} \vdash \mathrm{t}_{0}: \mathrm{T}_{0}$ as (1). We assume, w.l.o.g., $\overline{\mathrm{X}}_{0} \# \operatorname{ftv}(C, \mathrm{~T})(\mathbf{2})$ and $\mathrm{z}_{0} \notin f p i\left(\sigma_{0}\right)$ (3).

○ Case VAR. The rule's conclusion is $C \vdash \mathrm{x}: \mathrm{T}$ (4). Its premise is $C \Vdash \mathrm{x} \preceq$ $\mathrm{T}$ (5). Two subcases arise.

Subcase $\mathrm{x}$ is $\mathrm{z}_{0}$. Applying Sub to (1) yields $C_{0} \wedge \mathrm{T}_{0} \leq \mathrm{T} \vdash \mathrm{t}_{0}$ : T. By (2) and ExISTS, this implies $\exists \overline{\mathrm{X}}_{0} \cdot\left(C_{0} \wedge \mathrm{T}_{0} \leq \mathrm{T}\right) \vdash \mathrm{t}_{0}: \mathrm{T}$ (6). Furthermore, by (2) again, the constraint $\exists \overline{\mathrm{X}}_{0} \cdot\left(C_{0} \wedge \mathrm{T}_{0} \leq \mathrm{T}\right)$ is $\sigma_{0} \preceq \mathrm{T}$, which is equivalent to let $\mathrm{z}_{0}: \sigma_{0}$ in $\mathrm{z}_{0} \preceq \mathrm{T}$. As a result, (6) may be written let $\mathrm{z}_{0}: \sigma_{0}$ in $\mathrm{x} \preceq \mathrm{T} \vdash$ $\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{x}: \mathrm{T}(\mathbf{7})$.

Subcase $\mathrm{x}$ isn't $\mathrm{z}_{0}$. Then, $\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{x}$ is $\mathrm{x}$. Thus, VAR yields $\exists \sigma_{0} \wedge \mathrm{x} \preceq \mathrm{T} \vdash$ $\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{x}: \mathrm{T}$. By C-IN*, this may be read let $\mathrm{z}_{0}: \sigma_{0}$ in $\mathrm{x} \preceq \mathrm{T} \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{x}$ : $\mathrm{T}$, that is, again (7).

In either subcase, by (5), by congruence of entailment, and by Lemma 1.5.2, (7) implies let $\mathrm{z}_{0}: \sigma_{0}$ in $C \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}: \mathrm{T}$.
- Case ABs. The rule's conclusion is let $\mathrm{z}: \mathrm{T}$ in $C \vdash \lambda$ z.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$. Its premise is $C \vdash \mathrm{t}: \mathrm{T}^{\prime}(\mathbf{8})$. We may assume, w.l.o.g., that $\mathrm{z}$ is distinct from $\mathrm{z}_{0}$ and does not occur free within $t_{0}$ or $\sigma_{0}(9)$. Applying the induction hypothesis to (8) yields let $\mathrm{z}_{0}: \sigma_{0}$ in $C \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}: \mathrm{T}^{\prime}$, which, by ABs, implies let $\mathrm{z}: \mathrm{T}$ in (let $\mathrm{z}_{0}: \sigma_{0}$ in $\left.C\right) \vdash \lambda \mathrm{z}$. $\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$. By (9) and C-LETLet, this may be written let $\mathrm{z}_{0}: \sigma_{0}$ in (let $\mathrm{z}: \mathrm{T}$ in $\left.C\right) \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right](\lambda \mathrm{z} . \mathrm{t}): \mathrm{T} \rightarrow \mathrm{T}^{\prime}$.
- Case APp. By the induction hypothesis, by APP, and by C-InAnd.
- Case LET. The rule's conclusion is let $\mathrm{z}: \forall \overline{\mathrm{x}}_{1}\left[C_{1}\right] . \mathrm{T}_{1}$ in $C_{2} \vdash$ let $\mathrm{z}=$ $\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}_{2}$, where $\overline{\mathrm{x}}_{1}=\operatorname{ftv}\left(C_{1}, \mathrm{~T}_{1}\right)$. Its premises are $C_{1} \vdash \mathrm{t}_{1}: \mathrm{T}_{1}(\mathbf{1 0})$ and $C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}_{2}$ (11). We may assume, w.l.o.g., that $\mathrm{z}$ is distinct from $\mathrm{z}_{0}$ and does not occur free within $\mathrm{t}_{0}$ or $\sigma_{0}$ (12). We may also assume, w.l.o.g., $\overline{\mathrm{x}}_{1} \#$ $f t v\left(\sigma_{0}\right)$ (13). Applying the induction hypothesis to (10) and (11) respectively yields let $\mathrm{z}_{0}: \sigma_{0}$ in $C_{1} \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}_{1}: \mathrm{T}_{1}(\mathbf{1 4})$ and let $\mathrm{z}_{0}: \sigma_{0}$ in $C_{2} \vdash\left[\mathrm{z}_{0} \mapsto\right.$ $\left.\mathrm{t}_{0}\right] \mathrm{t}_{2}: \mathrm{T}_{2}$ (15). Applying LET to (14) and (15) produces let $\mathrm{z}: \forall \mathcal{V}\left[\right.$ let $\mathrm{z}_{0}:$ $\sigma_{0}$ in $\left.C_{1}\right] . \mathrm{T}_{1}$ in let $\mathrm{z}_{0}: \sigma_{0}$ in $C_{2} \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right]$ (let $\mathrm{z}=\mathrm{t}_{1}$ in $\left.\mathrm{t}_{2}\right): \mathrm{T}_{2}$ (16). Now, we have

$$
\begin{array}{ll} 
& \text { let } \mathrm{z}_{0}: \sigma_{0} ; \mathrm{z}: \forall \overline{\mathrm{X}}_{1}\left[C_{1}\right] \cdot \mathrm{T}_{1} \text { in } C_{2} \\
\equiv & \text { let } \mathrm{z}_{0}: \sigma_{0} ; \mathrm{z}: \forall \overline{\mathrm{X}}_{1}\left[\text { let } \mathrm{z}_{0}: \sigma_{0} \text { in } C_{1}\right] \cdot \mathrm{T}_{1} \text { in } C_{2} \\
\equiv & \text { let } \mathrm{z}: \forall \overline{\mathrm{X}}_{1}\left[\text { let } \mathrm{z}_{0}: \sigma_{0} \text { in } C_{1}\right] \cdot \mathrm{T}_{1} ; \mathrm{z}_{0}: \sigma_{0} \text { in } C_{2} \\
\Vdash & \text { let } \mathrm{z}: \forall \mathcal{V}\left[\text { let } \mathrm{z}_{0}: \sigma_{0} \text { in } C_{1}\right] \cdot \mathrm{T}_{1} ; \mathrm{z}_{0}: \sigma_{0} \text { in } C_{2} \tag{19}
\end{array}
$$

where (17) follows from (13), (3), and C-LETDup; (18) follows from (12) and C-LetLet; and (19) is by Lemma 1.3.25. Thus, applying Lemma 1.5.2 to (16) yields let $\mathrm{z}_{0}: \sigma_{0} ; \mathrm{z}: \forall \overline{\mathrm{x}}_{1}\left[C_{1}\right] . \mathrm{T}_{1}$ in $C_{2} \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right]$ (let $\mathrm{z}=\mathrm{t}_{1}$ in $\left.\mathrm{t}_{2}\right): \mathrm{T}_{2}$.
- Case Sub. By the induction hypothesis, by Sub, and by C-InAnd*.
- Case Exists. The rule's conclusion is $\exists \overline{\mathrm{x}} . C \vdash \mathrm{t}$ : T. Its premises are $C \vdash$ $\mathrm{t}: \mathrm{T}$ (20) and $\overline{\mathrm{X}} \# \mathrm{ftv}(\mathrm{T})$ (21). We may assume, w.l.o.g., $\overline{\mathrm{X}} \# \mathrm{ftv}\left(\sigma_{0}\right)$ (22). Applying the induction hypothesis to (20) yields let $\mathrm{z}_{0}: \sigma_{0}$ in $C \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}$ : $\mathrm{T}$, which, by (21) and ExisTs, implies $\exists \overline{\mathrm{x}}$. let $\mathrm{z}_{0}: \sigma_{0}$ in $C \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}: \mathrm{T}$ (23). By (22) and C-InEx, (23) is let $\mathrm{z}_{0}: \sigma_{0}$ in $\exists \overline{\mathrm{x}} . C \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}: \mathrm{T}$.

1.7.2 Lemma: let $\mathrm{z}: \forall \overline{\mathrm{X}}\left[\llbracket \mathrm{t}_{2}: \mathrm{T}_{2} \rrbracket\right] \cdot \mathrm{T}_{2}$ in $\llbracket \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket$ entails $\llbracket\left[\mathrm{z} \mapsto \mathrm{t}_{2}\right] \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket$.

Before going on, let us give a few definitions and formulate several requirements. First, we must define an initial environment $\Gamma_{0}$, which assigns a type scheme to every constant. A couple of requirements must be made to ensure that $\Gamma_{0}$ is consistent with the semantics of constants, as specified by $\xrightarrow{\delta}$. Second, we must extend constraint generation and well-typedness to configurations, as opposed to programs, since reduction operates on configurations.

Last, we must formulate a restriction to tame the interaction between side effects and let-polymorphism, which is unsound if unrestricted.

1.7.3 Definition: Let $\Gamma_{0}$ be an environment whose domain is the set of constants $\mathcal{Q}$. We require $f t v\left(\Gamma_{0}\right)=\varnothing$, fpi $\left(\Gamma_{0}\right)=\varnothing$, and $\exists \Gamma_{0} \equiv$ true. We refer to $\Gamma_{0}$ as the initial typing environment.

1.7.4 Definition: Let ref be an isolated, invariant type constructor of signature $\star \Rightarrow \star$. A store type $M$ is a finite mapping from memory locations to types. We write ref $M$ for the environment that maps $m$ to $\operatorname{ref} M(m)$ when $m$ is in the domain of $M$. Assuming $\operatorname{dom}(\mu)$ and $\operatorname{dom}(M)$ coincide, the constraint $\llbracket \mu: M \rrbracket$ is defined as the conjunction of the constraints $\llbracket \mu(m): M(m) \rrbracket$, where $m$ ranges over $\operatorname{dom}(\mu)$. Under the same assumption, the constraint $\llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket$ is defined as $\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \llbracket \mu: M \rrbracket$. A configuration $\mathrm{t} / \mu$ is well-typed if and only if there exist a type $\mathrm{T}$ and a store type $M$ such that $\operatorname{dom}(\mu)=\operatorname{dom}(M)$ and the constraint let $\Gamma_{0} ;$ ref $M$ in $\llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket$ is satisfiable.

The type ref $\mathrm{T}$ is the type of references (that is, memory locations) that store data of type T. It must be invariant in its parameter, reflecting the fact that references may be read and written.

A store is a complex object: it may contain values that indirectly refer to each other via memory locations. In fact, it is a representation of the graph formed by objects and pointers in memory, which may contain cycles. We rely on store types to deal with such cycles. In the definition of well-typedness, the store type $M$ imposes a constraint on the contents of the store - the value $\mu(m)$ must have type $M(m)$-but also plays the role of a hypothesis: by placing the constraint $\llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket$ within the context let ref $M$ in [], we give meaning to free occurrences of memory locations within $\llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket$, and stipulate that it is valid to assume that $m$ has type $M(m)$. In other words, we essentially view the store as a large, mutually recursive binding of locations to values. Since no satisfiable constraint may have a free program identifier (Lemma 1.3.31), every well-typed configuration must be closed. The context let $\Gamma_{0}$ in [] gives meaning to occurrences of constants within $\llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket$.

We now define a relation between configurations that plays a key role in the statement of the subject reduction property. The point of subject reduction is to guarantee that well-typedness is preserved by reduction. However, such a simple statement is too weak to be amenable to inductive proof. Thus, for the purposes of the proof, we must be more specific. To begin, let us consider the simpler case of a pure semantics, that is, a semantics without stores. Then, we must state that if an expression $t$ has type $T$ under a certain constraint, then its reduct $t^{\prime}$ has type $\mathrm{T}$ under the same constraint. In terms of generated constraints, this statement becomes: let $\Gamma_{0}$ in $\llbracket t: T \rrbracket$ entails let $\Gamma_{0}$ in $\llbracket t^{\prime}: \mathrm{T} \rrbracket$.

Let us now return to the general case, where a store is present. Then, the statement of well-typedness for a configuration $t / \mu$ involves a store type $M$ whose domain is that of $\mu$. So, the statement of well-typedness for its reduct $\mathrm{t}^{\prime} / \mu^{\prime}$ must involve a store type $M^{\prime}$ whose domain is that of $\mu^{\prime}$-which is larger if allocation occurred. The types of existing memory locations must not change: we must request that $M$ and $M^{\prime}$ agree on $\operatorname{dom}(M)$, that is, $M^{\prime}$ must extend $M$. Furthermore, the types assigned to new memory locations in $\operatorname{dom}\left(M^{\prime}\right) \backslash \operatorname{dom}(M)$ might involve new type variables, that is, variables that do not appear free in $M$ or T. We must allow these variables to be hidden-that is, existentially quantified - otherwise the entailment assertion cannot hold. These considerations lead us to the following definition:

1.7.5 Definition: $\mathrm{t} / \mu \sqsubseteq \mathrm{t}^{\prime} / \mu^{\prime}$ holds if and only if, for every type $\mathrm{T}$ and for every store type $M$ such that $\operatorname{dom}(\mu)=\operatorname{dom}(M)$, there exist a set of type variables $\overline{\mathrm{Y}}$ and a store type $M^{\prime}$ such that $\overline{\mathrm{Y}} \# f t v(\mathrm{~T}, M)$ and $f t v\left(M^{\prime}\right) \subseteq \overline{\mathrm{Y}} \cup f t v(M)$ and $\operatorname{dom}\left(M^{\prime}\right)=\operatorname{dom}\left(\mu^{\prime}\right)$ and $M^{\prime}$ extends $M$ and

$$
\begin{gathered}
\text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket \\
\Vdash \exists \overline{\mathrm{Y}} \text {.let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket \mathrm{t}^{\prime} / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket
\end{gathered}
$$

The relation $\sqsubseteq$ is intended to express a connection between a configuration and its reduct. Thus, subject reduction may be stated as: $(\longrightarrow) \subseteq(\sqsubseteq)$, that is, $\sqsubseteq$ is indeed a conservative description of reduction.

We have introduced an initial environment $\Gamma_{0}$ and used it in the definition of well-typedness, but we haven't yet ensured that the type schemes assigned to constants are an adequate description of their semantics. We now formulate two requirements that relate $\Gamma_{0}$ with $\xrightarrow{\delta}$. They are specializations of the subject reduction and progress properties to configurations that involve an application of a constant. They represent proof obligations that must be discharged when concrete definitions of $\mathcal{Q}, \xrightarrow{\delta}$, and $\Gamma_{0}$ are given.

1.7.6 Definition: We require (i) $(\xrightarrow{\delta}) \subseteq(\sqsubseteq)$; and (ii) if the configuration $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$ (where $k \geq 0$ ) is well-typed, then either it is reducible, or c $\mathrm{v}_{1} \ldots \mathrm{v}_{k}$ is a value.

The last point that remains to be settled before proving type soundness is the interaction between side effects and let-polymorphism. The following example illustrates the problem:

$$
\text { let } r=\text { ref } \lambda z . z \text { in let }{ }_{-}=(r:=\lambda z \cdot(z \hat{+} \hat{1})) \text { in } ! \text { true }
$$

This expression reduces to true $\hat{+} \hat{1}$, so it must not be well-typed. Yet, if natural type schemes are assigned to ref, !, and $:=$ (see Example 1.9.5), then
it is well-typed with respect to the rules given so far, because $\mathrm{r}$ receives the polymorphic type scheme $\forall \mathrm{X}$. $\operatorname{ref}(\mathrm{X} \rightarrow \mathrm{X})$, which allows writing a function of type int $\rightarrow$ int into $\mathrm{r}$ and reading it back with type bool $\rightarrow$ bool. The problem is that let-polymorphism simulates a textual duplication of the letbound expression ref $\lambda z . z$, while the semantics first reduces it to a value $m$, causing a new binding $m \mapsto \lambda z . z$ to appear in the store, then duplicates the address $m$. The new store binding is not duplicated: both copies of $m$ refer to the same memory cell. For this reason, generalization is unsound in this case, and must be restricted. Many authors have attempted to come up with a sound type system that accepts all pure programs and remains flexible enough in the presence of side effects (Tofte, 1988; Leroy, 1992). These proposals are often complex, which is why they have been abandoned in favor of an extremely simple syntactic restriction, known as the value restriction (Wright, 1995).

1.7.7 Definition: A program satisfies the value restriction if and only if all subexpressions of the form let $z=t_{1}$ in $t_{2}$ are in fact of the form let $z=v_{1}$ in $t_{2}$. In the following, we assume that either all constants have pure semantics, or all programs satisfy the value restriction.

Put slightly differently, the value restriction states that only values may be generalized. This eliminates the problem altogether, since duplicating values does not affect a program's semantics. Note that any program that does not satisfy the value restriction can be turned into one that does and has the same semantics: it suffices to change let $z=t_{1}$ in $t_{2}$ into $\left(\lambda z . t_{2}\right) t_{1}$ when $t_{1}$ is not a value. Of course, such a transformation may cause the program to become ill-typed. In other words, the value restriction causes some perfectly safe programs to be rejected. In particular, as stated above, it prevents generalizing applications of the form $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k}$, where $\mathrm{c}$ is a destructor of arity $k$. This is excessive, because many destructors have pure semantics; only a few, such as ref, allocate new mutable storage. Furthermore, we use pure destructors to encode numerous language features (Section 1.9). Fortunately, it is easy to relax the restriction to allow generalizing not only values, but also a more general class of nonexpansive expressions, whose syntax guarantees that such expressions cannot allocate new mutable storage (that is, expand the domain of the store). The term nonexpansive was coined by Tofte (1988). Nonexpansive expressions may include applications of the form $\mathrm{c} \mathrm{t}_{1} \ldots \mathrm{t}_{k}$, where $\mathrm{c}$ is a pure destructor of arity $k$ and $t_{1}, \ldots, t_{k}$ are nonexpansive. Experience shows that this slightly relaxed restriction is acceptable in practice. Some other improvements to the value restriction exist; see e.g. Exercise (Garrigue, 2002). Another frequent limitation of the value restriction are constructor functions, that is, functions that only build values, which are treated as ordinary functions and not as constructors, and their applications are not considered to be
values. For instance, in the expression let $f=c v$ in let $z=f$ w in $t$ where $\mathrm{c}$ is a constructor of arity 2, the partial application $\mathrm{c} v$ bound to $f$ is a constructor function (of arity 1 ), but $f \mathrm{w}$ is treated as a regular application and cannot be generalized. Technically, the effect of the (strict) value restriction is summarized by the following result.

1.7.8 Lemma: Under the value restriction, the production $\mathcal{E}::=$ let $\mathrm{z}=\mathcal{E}$ in $\mathrm{t}$ may be suppressed from the grammar of evaluation contexts (Figure 1-1) without altering the operational semantics.

We are done with definitions and requirements. We now come to the bulk of the type soundness proof.

1.7.9 THEOREM [SUBJECT REDUCTION]: $(\longrightarrow) \subseteq(\sqsubseteq)$.

Proof: Because $\longrightarrow$ and $\longrightarrow$ are the smallest relations that satisfy the rules of Figure 1-2, it suffices to prove that $\sqsubseteq$ satisfies these rules as well. We remark that if, for every type $\mathrm{T}, \llbracket \mathrm{t}: \mathrm{T} \rrbracket \Vdash \llbracket \mathrm{t}^{\prime}: \mathrm{T} \rrbracket$ holds, then $\mathrm{t} / \mu \sqsubseteq \mathrm{t}^{\prime} / \mu$ holds. (Take $\overline{\mathrm{Y}}=\varnothing$ and $M^{\prime}=M$ and use the fact that entailment is a congruence to check that the conditions of Definition 1.7.5 are met.) We make use of this fact in cases R-BETA and R-LET below.
- Case R-Beta. We have

$$
\begin{align*}
& \llbracket(\lambda z . t) \mathrm{v}: \mathrm{T} \rrbracket \\
\equiv & \exists \mathrm{x} .(\llbracket \lambda \mathrm{z} . \mathrm{t}: \mathrm{X} \rightarrow \mathrm{T} \rrbracket \wedge \llbracket \mathrm{v}: \mathrm{x} \rrbracket)  \tag{1}\\
\equiv & \exists \mathrm{x} .(\text { let } \mathrm{z}: \mathrm{X} \text { in } \llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \llbracket \mathrm{v}: \mathrm{x} \rrbracket)  \tag{2}\\
\equiv & \exists \mathrm{x} . \text { let } \mathrm{z}: \forall \varnothing[\llbracket \mathrm{v}: \mathrm{x} \rrbracket] . \mathrm{X} \text { in } \llbracket \mathrm{t}: \mathrm{T} \rrbracket  \tag{3}\\
\Vdash & \llbracket[\mathrm{z} \mapsto \mathrm{v}] \mathrm{t}: \mathrm{T} \rrbracket \tag{4}
\end{align*}
$$

where (1) is by definition of constraint generation; (2) is by Lemma 1.6.5; (3) is by C-LetAnd; (4) is by Lemma 1.7.2 and C-Ex*.
- Case R-LEt. We have

$$
\begin{align*}
& \llbracket \text { let } \mathrm{z}=\mathrm{v} \text { in } \mathrm{t}: \mathrm{T} \rrbracket \\
= & \text { let } \mathrm{z}: \forall \mathrm{x}[\llbracket \mathrm{v}: \mathrm{x} \rrbracket] \cdot \mathrm{X} \text { in } \llbracket \mathrm{t}: \mathrm{T} \rrbracket  \tag{1}\\
\mathbb{} & \llbracket[\mathrm{z} \mapsto \mathrm{v}] \mathrm{t}: \mathrm{T} \rrbracket \tag{2}
\end{align*}
$$

where (1) is by definition of constraint generation and (2) is by Lemma 1.7.2.
- Case R-Delta. This case is exactly requirement (i) in Definition 1.7.6.
- Case R-Extend. Our hypotheses are $\mathrm{t} / \mu \sqsubseteq \mathrm{t}^{\prime} / \mu^{\prime}(\mathbf{1})$ and $\operatorname{dom}\left(\mu^{\prime \prime}\right) \#$ $\operatorname{dom}\left(\mu^{\prime}\right)$ (2) and range( $\left.\mu^{\prime \prime}\right) \# \operatorname{dom}\left(\mu^{\prime} \backslash \mu\right)$ (3). Because $\operatorname{dom}(\mu)$ must be a subset of $\operatorname{dom}\left(\mu^{\prime}\right)$, it is also disjoint with $\operatorname{dom}\left(\mu^{\prime \prime}\right)$. Our goal is $\mathrm{t} / \mu \mu^{\prime \prime} \sqsubseteq$ $\mathrm{t}^{\prime} / \mu^{\prime} \mu^{\prime \prime}(4)$. Thus, let us introduce a type $\mathrm{T}$ and a store type of domain
$\operatorname{dom}\left(\mu \mu^{\prime \prime}\right)$, or (equivalently) two store types $M$ and $M^{\prime \prime}$ whose domains are respectively $\operatorname{dom}(\mu)$ and $\operatorname{dom}\left(\mu^{\prime \prime}\right)$. By (1), there exist type variables $\overline{\mathrm{Y}}$ and a store type $M^{\prime}$ such that $\overline{\mathrm{Y}} \# f t v(\mathrm{~T}, M)$ (5) and $f t v\left(M^{\prime}\right) \subseteq \overline{\mathrm{Y}} \cup f t v(M)$ and $\operatorname{dom}\left(M^{\prime}\right)=\operatorname{dom}\left(\mu^{\prime}\right)$ and $M^{\prime}$ extends $M$ (6) and let $\Gamma_{0}$; ref $M$ in $\llbracket \mathrm{t} / \mu$ : $\mathrm{T} / M \rrbracket \Vdash \exists \overline{\mathrm{Y}}$.let $\Gamma_{0}$; ref $M^{\prime}$ in $\llbracket \mathrm{t}^{\prime} / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket$. We may further require, w.l.o.g. $\overline{\mathrm{Y}} \# \operatorname{ftv}\left(M^{\prime \prime}\right)(7)$. Let us now add the conjunct let $\Gamma_{0} ; \operatorname{ref} M$ in $\llbracket \mu^{\prime \prime}: M^{\prime \prime} \rrbracket$ to each side of this entailment assertion. On the left-hand side, by C-InAnd and by Definition 1.7.4, we obtain let $\Gamma_{0}$; ref $M$ in $\llbracket \mathrm{t} / \mu \mu^{\prime \prime}: \mathrm{T} / M M^{\prime \prime} \rrbracket$ (8). On the right-hand side, by (5), (7), C-ExAnd, and C-InAnd, we obtain $\exists \overline{\mathrm{Y}}$.let $\Gamma_{0}$ in (let ref $M^{\prime}$ in $\llbracket \mathrm{t}^{\prime} / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket \wedge$ let ref $M$ in $\left.\llbracket \mu^{\prime \prime}: M^{\prime \prime} \rrbracket\right)$ (9). Now, recall that $M^{\prime}$ extends $M$ (6) and, furthermore, (3) implies $f p i\left(\llbracket \mu^{\prime \prime}\right.$ : $\left.M^{\prime \prime}\right)$ \# $d p i\left(M^{\prime} \backslash M\right)$ (10). By (10), C-InAnd*, and C-InAnd, (9) is equivalent to $\exists \bar{Y}$.let $\Gamma_{0} ;$ ref $M^{\prime}$ in $\left(\llbracket \mathrm{t}^{\prime} / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket \wedge \llbracket \mu^{\prime \prime}: M^{\prime \prime} \rrbracket\right)$, that is, $\exists \bar{Y}$.let $\Gamma_{0}$; ref $M^{\prime}$ in $\llbracket \mathrm{t}^{\prime} / \mu^{\prime} \mu^{\prime \prime}: \mathrm{T} / M^{\prime} M^{\prime \prime} \rrbracket$ (11). Thus, we have established that (8) entails (11). Let us now place this entailment assertion within the constraint context let ref $M^{\prime \prime}$ in $\square$. On the left-hand side, because $f p i\left(\Gamma_{0}, M, M^{\prime \prime}\right)=\varnothing$ and $d p i\left(M^{\prime \prime}\right) \cap d p i\left(\Gamma_{0}, M\right) \subseteq \operatorname{dom}\left(\mu^{\prime \prime}\right) \cap(\mathcal{Q} \cup \operatorname{dom}(\mu))=$ $\varnothing$, C-LetLet applies, yielding let $\Gamma_{0}$; ref $M M^{\prime \prime}$ in $\llbracket \mathrm{t} / \mu \mu^{\prime \prime}: \mathrm{T} / M M^{\prime \prime} \rrbracket(\mathbf{1 2})$. On the right-hand side, by (7), C-InEx, and by analogous reasoning, we obtain $\exists \overline{\mathrm{Y}}$.let $\Gamma_{0}$; ref $M^{\prime} M^{\prime \prime}$ in $\llbracket \mathrm{t}^{\prime} / \mu^{\prime} \mu^{\prime \prime}: \mathrm{T} / M^{\prime} M^{\prime \prime} \rrbracket$ (13). Thus, (12) entails (13). Given (5), (7), given $f t v\left(M^{\prime} M^{\prime \prime}\right) \subseteq \overline{\mathrm{Y}} \cup f t v\left(M M^{\prime \prime}\right)$, and given that $M^{\prime} M^{\prime \prime}$ extends $M M^{\prime \prime}$, this establishes the goal (4).
- Case R-Context. The hypothesis is $\mathrm{t} / \mu \sqsubseteq \mathrm{t}^{\prime} / \mu^{\prime}$. The goal is $\mathcal{E}[\mathrm{t}] / \mu \sqsubseteq$ $\mathcal{E}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}$. Because $\longrightarrow$ relates closed configurations only, we may assume that the configuration $\mathcal{E}[\mathrm{t}] / \mu$ is closed, so the memory locations that appear free within $\mathcal{E}$ are members of $\operatorname{dom}(\mu)$. Let us now reason by induction on the structure of $\mathcal{E}$.

Subcase $\mathcal{E}=[]$. The hypothesis and the goal coincide.

Subcase $\mathcal{E}=\mathcal{E}_{1} \mathrm{t}_{1}$. The induction hypothesis is $\mathcal{E}_{1}[\mathrm{t}] / \mu \sqsubseteq \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}$ (1). Let us introduce a type $\mathrm{T}$ and a store type $M$ such that $\operatorname{dom}(M)=\operatorname{dom}(\mu)$. Consider the constraint let $\Gamma_{0} ; \operatorname{ref} M$ in $\llbracket \mathcal{E}[\mathrm{t}] / \mu: \mathrm{T} / M \rrbracket(2)$. By definition of constraint generation, C-ExAnd, C-InEx, and C-InAnd, it is equivalent to

\section*{$\exists \mathrm{X}$.(let $\Gamma_{0} ; \operatorname{ref} M$ in $\llbracket \mathcal{E}_{1}[\mathrm{t}] / \mu: \mathrm{X} \rightarrow \mathrm{T} / M \rrbracket \wedge$ let $\Gamma_{0} ; \operatorname{ref} M$ in $\left.\llbracket \mathrm{t}_{1}: \mathrm{X} \rrbracket\right)(\mathbf{3})$}

where $\mathrm{X} \notin f t v(\mathrm{~T}, M)$ (4). By (1), there exist type variables $\overline{\mathrm{Y}}$ and a store type $M^{\prime}$ such that $\overline{\mathrm{Y}} \# f t v(\mathrm{X}, \mathrm{T}, M)$ (5) and $f t v\left(M^{\prime}\right) \subseteq \overline{\mathrm{Y}} \cup f t v(M)$ (6) and $\operatorname{dom}\left(M^{\prime}\right)=\operatorname{dom}\left(\mu^{\prime}\right)$ and $M^{\prime}$ extends $M$ and (3) entails

$$
\exists \mathrm{X} .\left(\exists \overline{\mathrm{Y}} . \text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}: \mathrm{X} \rightarrow \mathrm{T} / M^{\prime} \rrbracket \wedge \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket \mathrm{t}_{1}: \mathrm{X} \rrbracket\right)(7)
$$

We pointed out earlier that the memory locations that appear free in $t_{1}$ are members of $\operatorname{dom}(M)$, which implies let ref $M$ in $\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket \equiv$ let ref $M^{\prime}$ in $\llbracket \mathrm{t}_{1}$ :

X】 (8). By (5), C-ExAnd, (8), C-InAnd, and by definition of constraint generation, we find that (7) is equivalent to

$$
\exists \mathrm{x} \bar{Y} \text {.let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in }\left(\llbracket \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right]: \mathrm{X} \rightarrow \mathrm{T} \rrbracket \wedge \llbracket \mathrm{t}_{1}: \mathrm{X} \rrbracket \wedge \llbracket \mu^{\prime}: M^{\prime} \rrbracket\right)(\mathbf{9}) \text {. }
$$

(4), (5) and (6) imply $\mathrm{X} \notin f t v\left(M^{\prime}\right)$. Thus, by C-InEx and C-ExAnd, (9) may be written

$$
\exists \overline{\mathrm{Y}} \text {.let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in }\left(\exists \mathrm{x} .\left(\llbracket \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right]: \mathrm{X} \rightarrow \mathrm{T} \rrbracket \wedge \llbracket \mathrm{t}_{1}: \mathrm{X} \rrbracket\right) \wedge \llbracket \mu^{\prime}: M^{\prime} \rrbracket\right) \text {, }
$$

which, by definition of constraint generation, is

$$
\exists \bar{Y} \text {.let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket \mathcal{E}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket(\mathbf{1 0}) \text {. }
$$

Thus, we have proved that (2) entails (10). By Definition 1.7.5, this establishes $\mathcal{E}[\mathrm{t}] / \mu \sqsubseteq \mathcal{E}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}$.

Subcase $\mathcal{E}=\mathrm{v} \mathcal{E}_{1}$. Analogous to the previous subcase.

Subcase $\mathcal{E}=$ let $\mathrm{z}=\mathcal{E}_{1}$ in $\mathrm{t}_{1}$. The induction hypothesis is $\mathcal{E}_{1}[\mathrm{t}] / \mu \sqsubseteq$ $\mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}(\mathbf{1})$. This subcase is particularly interesting, because it is where let-polymorphism and side effects interact. In the previous two subcases, we relied on the fact that the $\exists \bar{Y}$ quantifier, which hides the types of the memory cells created by the reduction step, commutes with the connectives $\exists$ and $\wedge$ introduced by application contexts. However, it does not in general (left)commute with the let connective (Example 1.3.28). Fortunately, under the value restriction, this subcase never arises (Lemma 1.7.8). By Definition 1.7.7, this subcase may arise only if all constants have pure semantics, which implies $\mu=\mu^{\prime}=\varnothing$. Then, we have

$$
\begin{align*}
& \text { let } \Gamma_{0} \text { in } \llbracket \mathcal{E}[\mathrm{t}]: \mathrm{T} \rrbracket \\
= & \text { let } \Gamma_{0} ; \mathrm{z}: \forall \mathrm{X}\left[\llbracket \mathcal{E}_{1}[\mathrm{t}]: \mathrm{X} \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket  \tag{2}\\
\equiv & \text { let } \Gamma_{0} ; \mathrm{z}: \forall \mathrm{X}\left[\text { let } \Gamma_{0} \text { in } \llbracket \mathcal{E}_{1}[\mathrm{t}]: \mathrm{x} \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket  \tag{3}\\
\Vdash & \text { let } \Gamma_{0} ; \mathrm{z}: \forall \mathrm{X}\left[\text { let } \Gamma_{0} \text { in } \llbracket \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right]: \mathrm{X} \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket  \tag{4}\\
\equiv & \text { let } \Gamma_{0} \text { in } \llbracket \mathcal{E}\left[\mathrm{t}^{\prime}\right]: \mathrm{T} \rrbracket \tag{5}
\end{align*}
$$

where (2) is by definition of constraint generation; (3) follows from $f t v\left(\Gamma_{0}\right)=$ $f p i\left(\Gamma_{0}\right)=\varnothing$ and C-LETDup; (4) follows from (1), specialized to the case of a pure semantics; and (5) is obtained by performing these steps in reverse.

1.7.10 Exercise [Recommended, $\star \star \star$ ]: Try to carry out the last subcase of the above proof in the case of an impure semantics and in the absence of the value restriction. Find out why it fails. Show that it succeeds if $\bar{Y}$ is assumed to be empty. Use this fact to prove that generalization is still safe when restricted to nonexpansive expressions, provided (i) evaluating a nonexpansive expression
cannot cause new memory cells to be allocated, (ii) nonexpansive expressions are stable by substitution of values for variables, and (iii) nonexpansive expressions are preserved by reduction.

Subject reduction ensures that well-typedness is preserved by reduction.

1.7.11 Lemma: Let $t / \mu \longrightarrow t^{\prime} / \mu^{\prime}$. If $t / \mu$ is well-typed, then so is $t^{\prime} / \mu^{\prime}$.

Proof: Assume $t / \mu \longrightarrow t^{\prime} / \mu^{\prime}$ (1) and $t / \mu$ is well-typed (2). By (2) and Definition 1.7.4, there exist a type $\mathrm{T}$ and a store type $M$ such that $\operatorname{dom}(\mu)=$ $\operatorname{dom}(M)$ and the constraint let $\Gamma_{0} ; \operatorname{ref} M$ in $\llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket(3)$ is satisfiable. By Theorem 1.7.9 and Definition 1.7.5, (1) implies that there exist a set of type variables $\overline{\mathrm{Y}}$ and a store type $M^{\prime}$ such that $\operatorname{dom}\left(M^{\prime}\right)=\operatorname{dom}\left(\mu^{\prime}\right)(\mathbf{4})$ and the constraint (3) entails $\exists \overline{\mathrm{Y}}$.let $\Gamma_{0}$; ref $M^{\prime}$ in $\llbracket \mathrm{t}^{\prime} / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket$ (5). Because (3) is satisfiable, so is (5), which implies that let $\Gamma_{0}$; ref $M^{\prime}$ in $\llbracket \mathrm{t}^{\prime} / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket$ is satisfiable (6). By (4) and (6) and Definition 1.7.4, $t^{\prime} / \mu^{\prime}$ is well-typed.

Let us now establish the progress property.

1.7.12 Lemma: If $t_{1} t_{2}$ is well-typed, then $t_{1} / \mu$ and $t_{2} / \mu$ are well-typed. If let $z=$ $t_{1}$ in $t_{2} / \mu$ is well-typed, then $t_{1} / \mu$ is well-typed.

1.7.13 Theorem [Progress]: If $t / \mu$ is well-typed, then either it is reducible, or $t$ is a value.

Proof: The proof is by induction on the structure of $t$.
- Case $\mathrm{t}=\mathrm{z}$. Well-typed configurations are closed: this case cannot occur.
- Case $\mathrm{t}=m$. $\mathrm{t}$ is a value.
- Case $\mathrm{t}=\mathrm{c}$. By requirement (ii) of Definition 1.7.6.

$\circ$ Case $\mathrm{t}=\lambda$ z.t $\mathrm{t}_{1} . \mathrm{t}$ is a value.
- Case $\mathrm{t}=\mathrm{t}_{1} \mathrm{t}_{2}$. By Lemma 1.7.12, $\mathrm{t}_{1} / \mu$ is well-typed. By the induction hypothesis, either it is reducible, or $\mathrm{t}_{1}$ is a value. If the former, by $\mathrm{R}$-CONTEXT and because every context of the form $\mathcal{E} t_{2}$ is an evaluation context, the configuration $t / \mu$ is reducible as well. Thus, let us assume $t_{1}$ is a value. By Lemma 1.7.12, $\mathrm{t}_{2} / \mu$ is well-typed. By the induction hypothesis, either it is reducible, or $t_{2}$ is a value. If the former, by $\mathrm{R}$-CONTEXT and because every context of the form $t_{1} \mathcal{E}$ - where $t_{1}$ is a value - is an evaluation context, the configuration $t / \mu$ is reducible as well. Thus, let us assume $t_{2}$ is a value. Let us now reason by cases on the structure of $t_{1}$.

Subcase $\mathrm{t}_{1}=\mathrm{z}$. Again, this subcase cannot occur.

Subcase $t_{1}=m$. Because $t / \mu$ is well-typed, a constraint of the form let $\Gamma_{0}$; ref $M$ in $\left(\exists \mathrm{x} .\left(m \preceq \mathrm{X} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{t}_{2}: \mathrm{x} \rrbracket\right) \wedge \llbracket \mu: M \rrbracket\right)$ must be satisfiable. This implies that $m$ is a member of $\operatorname{dom}(M)$ and that the constraint
ref $M(m) \leq \mathrm{X} \rightarrow \mathrm{T}$ is satisfiable. Because the type constructors ref and $\rightarrow$ are incompatible, this is a contradiction. So, this subcase cannot occur.

Subcase $\mathrm{t}_{1}=\lambda \mathrm{z} \mathrm{t}_{1}^{\prime}$. By R-BETA, $\mathrm{t} / \mu$ is reducible.

Subcase $\mathrm{t}_{1}=\mathrm{cv}_{1} \ldots \mathrm{v}_{k}$. Then, $\mathrm{t}$ is of the form $\mathrm{c}_{1} \ldots \mathrm{v}_{k+1}$. The result follows by requirement (ii) of Definition 1.7.6.
- Case $\mathrm{t}=$ let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}$. By Lemma 1.7.12, $\mathrm{t}_{1} / \mu$ is well-typed. By the induction hypothesis, either $t_{1} / \mu$ is reducible, or $t_{1}$ is a value. If the former, by $\mathrm{R}$-CONTEXT and because every context of the form let $\mathrm{z}=\mathcal{E}$ in $\mathrm{t}_{2}$ is an evaluation context, the configuration $t / \mu$ is reducible as well. If the latter, then $t / \mu$ is reducible by $\mathrm{R}$-LET.

We may now conclude:

1.7.14 Theorem [Type Soundness]: Well-typed source programs do not go wrong.

Proof: We say that a source program $t$ is well-typed if and only if the configuration $t / \varnothing$ is well-typed, that is, if and only if $\exists \mathrm{X}$.let $\Gamma_{0}$ in $\llbracket t: \mathrm{x} \rrbracket \equiv$ true holds. By Lemma 1.7.11, all reducts of $t / \varnothing$ are well-typed. By Theorem 1.7.13, none is stuck.

Let us recall that this result holds only if the requirements of Definition 1.7.6 are met. In other words, some proof obligations remain to be discharged when concrete definitions of $\mathcal{Q}, \xrightarrow{\delta}$, and $\Gamma_{0}$ are given. This is illustrated by several examples in the next section.

\subsection*{1.8 Constraint solving}

We have introduced a parameterized constraint language, given equivalence laws that describe the interaction between its logical connectives, and exploited them to prove theorems about type inference and type soundness, which are valid independently of the nature of primitive constraints- the socalled predicate applications. However, there would be little point in proposing a parameterized constraint solver, because much of the difficulty of designing an efficient constraint solver precisely lies in the treatment of primitive constraints and in its interaction with let-polymorphism. For this reason, in this section, we focus on constraint solving in the setting of an equality-only free tree model. Thus, the constraint solver developed here allows performing type inference for $\mathrm{HM}(=)$ (that is, for Damas and Milner's type system) and for its extension with recursive types. Of course, some of its mechanisms may be useful in other settings. Other constraint solvers used in program analysis or type inference are described e.g. in (Aiken and Wimmers, 1992; Niehren,

Müller, and Podelski, 1997; Fähndrich, 1999; Melski and Reps, 2000; Müller, Niehren, and Treinen, 2001; Pottier, 2001b; Nielson, Nielson, and Seidl, 2002; McAllester, 2002, 2003).

We begin with a rule-based presentation of a standard, efficient first-order unification algorithm. This yields a constraint solver for a subset of the constraint language, deprived of type scheme introduction and instantiation forms. On top of it, we build a full constraint solver, which corresponds to the code that accompanies this chapter.

\section*{Unification}

Unification is the process of solving equations between terms. We now present a unification algorithm due to Huet (1976) as a (nondeterministic) system of constraint rewriting rules. The specification is almost the same in the case of finite and regular tree models: only one rule, which implements the occurs check, must be removed in the latter case. In other words, the algorithm works with possibly cyclic terms, and does not rely in an essential way on the occurs check. In order to accurately reflect the behavior of the actual algorithm, which relies on a union-find data structure (Tarjan, 1975), we modify the syntax of constraints by replacing equations with multi-equations. A multi-equation is an equation that involves an arbitrary number of types, as opposed to exactly two.

1.8.1 Definition: Let there be, for every kind $\kappa$ and for every $n \geq 1$, a predicate ${ }_{\kappa}^{n}$, of signature $\kappa^{n} \Rightarrow \cdot$, whose interpretation is ( $n$-ary) equality. The predicate constraint $={ }_{\kappa}^{n} \mathrm{~T}_{1} \ldots \mathrm{T}_{n}$ is written $\mathrm{T}_{1}=\ldots=\mathrm{T}_{n}$, and called a multi-equation. We consider the constraint true as a multi-equation of length 0 . In the following, we identify multi-equations up to permutations of their members, so a multi-equation $\epsilon$ of kind $\kappa$ may be viewed as a finite multiset of types of kind $\kappa$. We write $\epsilon=\epsilon^{\prime}$ for the multi-equation obtained by concatenating $\epsilon$ and $\epsilon^{\prime}$.

Thus, we are interested in the following subset of the constraint language:

$$
U::=\text { true } \mid \text { false }|\epsilon| U \wedge U \mid \exists \overline{\mathrm{X}} . U
$$

Equations are replaced with multi-equations; no other predicates are available. Type scheme introduction and instantiation forms are absent.

1.8.2 Definition: A multi-equation is standard if and only if its variable members are distinct and it has at most one nonvariable member. A constraint $U$ is standard if and only if every multi-equation inside $U$ is standard and every variable that occurs (free or bound) in $U$ is a member of at most one multiequation inside $U$.

A union-find algorithm maintains equivalence classes (that is, disjoint sets) of variables, and associates, with each class, a descriptor, which in our case is either absent or a nonvariable term. Thus, a standard constraint represents a state of the union-find algorithm. A constraint that is not standard may be viewed as a superposition of a state of the union-find algorithm, on the one hand, and of control information, on the other hand. For instance, a multi-equation of the form $\epsilon=\mathrm{T}_{1}=\mathrm{T}_{2}$, where $\mathrm{T}_{1}$ and $\mathrm{T}_{2}$ are nonvariable terms, may be viewed, roughly speaking, as the equivalence class $\epsilon=\mathrm{T}_{1}$, together with a pending request to solve $\mathrm{T}_{1}=\mathrm{T}_{2}$ and to update the class's descriptor accordingly. Because multi-equations encode both state and control, our specification of unification is rather high-level. It would be possible to give a lower-level description, where state (standard conjunctions of multiequations) and control (pending binary equations) are distinguished.

1.8.3 Definition: Let $U$ be a conjunction of multi-equations. $\mathrm{Y}$ is dominated by $\mathrm{X}$ with respect to $U$ (written: $\mathrm{Y} \prec_{U} \mathrm{X}$ ) if and only if $U$ contains a conjunct of the form $\mathrm{X}=F \overrightarrow{\mathrm{T}}=\epsilon$, where $\mathrm{Y} \in f t v(\overline{\mathrm{T}}) . U$ is cyclic if and only if the graph of $\prec_{U}$ exhibits a cycle.

The specification of the unification algorithm consists of a set of constraint rewriting rules, given in Figure 1-11. Rewriting is performed modulo $\alpha$-conversion, modulo permutations of the members of a multi-equation, modulo commutativity and associativity of conjunction, and under an arbitrary context. The specification is nondeterministic: several rule instances may be simultaneously applicable.

S-ExAnd is a directed version of C-ExAnd, whose effect is to float up all existential quantifiers. In the process, all multi-equations become part of a single conjunction, possibly causing rules whose left-hand side is a conjunction of multi-equations, namely S-FUSE and S-CYCLE, to become applicable. S-FUSE identifies two multi-equations that share a common variable $\mathrm{X}$, and fuses them. The new multi-equation is not necessarily standard, even if the two original multi-equations were. Indeed, it may have repeated variables or contain two nonvariable terms. The purpose of the next few rules, whose lefthand side consists of a single multi-equation, is to deal with these situations. S-STUTTER eliminates redundant variables. It only deals with variables, as opposed to terms of arbitrary size, so as to have constant time cost. The comparison of nonvariable terms is implemented by S-DECOMPOSE and SClash. S-Decompose decomposes an equation between two terms whose head symbols match. It produces a conjunction of equations between their subterms, namely $\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}$. Only one of the two terms remains in the original multi-equation, which may thus become standard. The terms $\overrightarrow{\mathrm{X}}$ are copiedthere are two occurrences of $\overrightarrow{\mathrm{X}}$ on the right-hand side. For this reason, we

$$
\begin{aligned}
& \left(\exists \overline{\mathrm{X}} \cdot U_{1}\right) \wedge U_{2} \quad \rightarrow \quad \exists \overline{\mathrm{x}} \cdot\left(U_{1} \wedge U_{2}\right) \\
& \text { if } \overline{\mathrm{x}} \# \operatorname{ftv}\left(U_{2}\right) \\
& \mathrm{X}=\epsilon \wedge \mathrm{X}=\epsilon^{\prime} \quad \rightarrow \quad \mathrm{X}=\epsilon=\epsilon^{\prime} \\
& \mathrm{X}=\mathrm{X}=\epsilon \quad \rightarrow \quad \mathrm{X}=\epsilon \\
& F \overrightarrow{\mathrm{x}}=F \overrightarrow{\mathrm{T}}=\epsilon \quad \rightarrow \quad \overrightarrow{\mathrm{x}}=\overrightarrow{\mathrm{T}} \wedge F \overrightarrow{\mathrm{x}}=\epsilon \\
& F \mathrm{~T}_{1} \ldots \mathrm{T}_{i} \ldots \mathrm{T}_{n}=\epsilon \quad \rightarrow \quad \exists \mathrm{X} .\left(\mathrm{X}=\mathrm{T}_{i} \wedge F \mathrm{~T}_{1} \ldots \mathrm{X} \ldots \mathrm{T}_{n}=\epsilon\right) \\
& \text { if } \mathrm{T}_{i} \notin \mathcal{V} \wedge \mathrm{X} \notin f t v\left(\mathrm{~T}_{1}, \ldots, \mathrm{T}_{n}, \epsilon\right) \\
& F \overrightarrow{\mathrm{T}}=F^{\prime} \overrightarrow{\mathrm{T}}^{\prime}=\epsilon \quad \rightarrow \quad \text { false } \\
& \text { if } F \neq F^{\prime} \\
& \mathrm{T} \rightarrow \text { true } \\
& \text { if } \mathrm{T} \notin \mathcal{V} \\
& U \wedge \text { true } \rightarrow U \\
& U \rightarrow \text { false } \\
& \text { if the model is syntactic and } U \text { is cyclic } \\
& \mathcal{U}[\text { false }] \rightarrow \text { false } \\
& \text { if } \mathcal{U} \neq[]
\end{aligned}
$$

\section*{Figure 1-11: Unification}

require them to be type variables, as opposed to terms of arbitrary size. (We slightly abuse notation by using $\overrightarrow{\mathrm{x}}$ to denote a vector of type variables whose elements are not necessarily distinct.) By doing so, we allow explicitly reasoning about sharing: since a variable represents a pointer to an equivalence class, we explicitly specify that only pointers, not whole terms, are copied. As a result of this decision, $\mathrm{S}$-DECOMPOSE is not applicable when both terms at hand have a nonvariable subterm. S-NAME- 1 remedies this problem by introducing a fresh variable that stands for one such subterm. When repeatedly applied, S-NAME-1 yields a unification problem composed of so-called small terms only - that is, where sharing has been made fully explicit. S-CLASH complements S-DECOmpose by dealing with the case where two terms with different head symbols are equated; in a free tree model, such an equation is false, so failure is signaled. S-SingLE and S-TRUE suppress multi-equations of size 1 and 0 , respectively, which are tautologies. S-SINGLE is restricted to nonvariable terms so as not to break the property that every variable is a member
of exactly one multi-equation (Definition 1.8.2). S-CYCLE is the occurs check: that is, it signals failure if the constraint is cyclic. It is applicable only in the case of syntactic unification, that is, when ground types are finite trees. It is a global check: its left-hand side is an entire conjunction of multi-equations.

S-FAIL propagates failure; $\mathcal{U}$ ranges over unification constraint contexts.

The constraint rewriting system in Figure 1-11 enjoys the following properties. First, rewriting is strongly normalizing, so the rules define a (nondeterministic) algorithm. Second, rewriting is meaning-preserving. Third, every normal form is either false or of the form $\exists \overline{\mathrm{X}} . U$, where $U$ is satisfiable. The latter two properties indicate that the algorithm is indeed a constraint solver.

1.8.4 Lemma: The rewriting system $\rightarrow$ is strongly normalizing.

1.8.5 Lemma: $U_{1} \rightarrow U_{2}$ implies $U_{1} \equiv U_{2}$.

1.8.6 Lemma: Every normal form is either false or of the form $\mathcal{X}[U]$, where $\mathcal{X}$ is an existential constraint context, $U$ is a standard conjunction of multi-equations and, if the model is syntactic, $U$ is acyclic. These conditions imply that $U$ is satisfiable.

\section*{A constraint solver}

On top of the unification algorithm, we now define a constraint solver. Its specification is independent of the rules and strategy employed by the unification algorithm. However, the structure of the unification algorithm's normal forms, as well as the logical properties of multi-equations, are exploited when performing generalization, that is, when creating and simplifying type schemes. Like the unification algorithm, the constraint solver is specified in terms of a reduction system. However, the objects that are subject to rewriting are not just constraints: they have more complex structure. Working with such richer states allows distinguishing the solver's external language - namely, the full constraint language, which is used to express the problem that one wishes to solve - and an internal language, introduced below, which is used to describe the solver's private data structures. In the following, $C$ and $D$ range over external constraints, that is, constraints that were part of the solver's input. External constraints are to be viewed as abstract syntax trees, subject to no implicit laws other than $\alpha$-conversion. As a simplifying assumption, we require external constraints not to contain any occurrence of false-otherwise the problem at hand is clearly false. Internal data structures include unification constraints $U$, as previously studied, and stacks. Stacks form a subset of constraint contexts, defined on page 24. Their syntax is as follows:

$$
S::=\square|S[[] \wedge C]| S[\exists \overline{\mathrm{x}} .[]] \mid S[\text { let } \mathrm{x}: \forall \overline{\mathrm{x}}[[]] . \mathrm{T} \text { in } C] \mid S[\text { let } \mathrm{x}: \sigma \text { in []] }
$$

In the second and fourth productions, $C$ is an external constraint. In the last production, we require $\sigma$ to be of the form $\forall \overline{\mathrm{X}}[U]$.X, and we demand $\exists \sigma \equiv$ true. A stack may be viewed as a list of frames. Frames may be added and deleted at the inner end of a stack, that is, near the hole of the constraint context that it represents. We refer to the four kinds of frames as conjunction, existential, let, and environment frames, respectively. A state of the constraint solver is a triple $S ; U ; C$, where $S$ is a stack, $U$ is a unification constraint, and $C$ is an external constraint. The state $S ; U ; C$ is to be understood as a representation of the constraint $S[U \wedge C]$. The notion of $\alpha$-equivalence between states is defined accordingly. In particular, one may rename type variables in $d t v(S)$, provided $U$ and $C$ are renamed as well. In short, the three components of a state play the following roles. $C$ is an external constraint that the solver intends to examine next. $U$ is the internal state of the underlying unification algorithm: one might think of it as the knowledge that has been obtained so far. $S$ tells where the type variables that occur free in $U$ and $C$ are bound, associates type schemes with the program variables that occur free in $C$, and records what should be done after $C$ is solved. The solver's initial state is usually of the form []; true; $C$, where $C$ is the external constraint that one wishes to solve-that is, whose satisfiability one wishes to determine. For simplicity, we make the (unessential) assumption that states have no free type variables.

The solver consists of a (nondeterministic) state rewriting system, given in Figure 1-12. Rewriting is performed modulo $\alpha$-conversion. S-UNIFY makes the unification algorithm a component of the constraint solver, and allows the current unification problem $U$ to be solved at any time. Rules S-Ex-1 to SEx-4 float existential quantifiers out of the unification problem into the stack, and through the stack up to the nearest enclosing let frame, if there is any, or to the outermost level, otherwise. Their side-conditions prevent capture of type variables, and may always be satisfied by suitable $\alpha$-conversion of the left-hand state. If $S ; U ; C$ is a normal form with respect to the above five rules, then every type variable in $d t v(S)$ is either universally quantified at a let frame, or existentially bound at the outermost level. (Recall that, by assumption, states have no free type variables.) In other words, provided these rules are applied in an eager fashion, there is no need for existential frames to appear in the machine representation of stacks. Instead, it suffices to maintain, at every let frame and at the outermost level, a list of the type variables that are bound at this point; and, conversely, to annotate every type variable in $d t v(S)$ with an integer rank, which allows telling, in constant time, where the variable is bound: type variables of rank 0 are bound at the outermost level, and type variables of rank $k \geq 1$ are bound at the $k^{\text {th }}$ let frame down in the stack $S$. The code that accompanies this chapter adopts this convention. Ranks were

\begin{tabular}{|c|c|c|c|}
\hline$S ; U ; C$ & $\rightarrow$ & \begin{tabular}{l}
$S ; U^{\prime} ; C$ \\
if $U \rightarrow U^{\prime}$
\end{tabular} & (S-UNIFY) \\
\hline$S ; \exists \overline{\mathrm{x}} . U ; C$ & $\rightarrow$ & \begin{tabular}{l}
$S[\exists \overline{\mathrm{X}} .[]] ; U ; C$ \\
if $\overline{\mathrm{x}} \# \operatorname{ftv}(C)$
\end{tabular} & $(\mathrm{S}-\mathrm{Ex}-1)$ \\
\hline$S[(\exists \overline{\mathrm{x}} \cdot \square) \wedge C]$ & $\rightarrow$ & \begin{tabular}{l}
$S[\exists \overline{\mathrm{X}} .(\square \wedge C)]$ \\
if $\overline{\mathrm{x}} \# \operatorname{ftv}(C)$
\end{tabular} & $(\mathrm{S}-\mathrm{Ex}-2)$ \\
\hline$S[$ let x : $\forall \overline{\mathrm{X}}[\exists \overline{\mathrm{Y}} .[]] . \mathrm{T}$ in $C]$ & $\rightarrow$ & \begin{tabular}{l}
$S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}} \overline{\mathrm{Y}}[[]] \cdot \mathrm{T}$ in $C]$ \\
if $\overline{\mathrm{Y}} \# \operatorname{ftv}(\mathrm{T})$
\end{tabular} & $(\mathrm{S}-\mathrm{Ex}-3)$ \\
\hline$S[$ let $\mathrm{x}: \sigma$ in $\exists \overline{\mathrm{x}} .[]]$ & $\rightarrow$ & \begin{tabular}{l}
$S[\exists \overline{\mathrm{X}}$.let $\mathrm{x}: \sigma$ in []$]$ \\
if $\overline{\mathrm{x}} \# \operatorname{ftv}(\sigma)$
\end{tabular} & $(\mathrm{S}-\mathrm{Ex}-4)$ \\
\hline$S ; U ; \mathrm{T}_{1}=\mathrm{T}_{2}$ & $\rightarrow$ & $S ; U \wedge \mathrm{T}_{1}=\mathrm{T}_{2} ;$ true & (S-SolvE-EQ) \\
\hline$S ; U ; \mathrm{x} \preceq \mathrm{T}$ & $\rightarrow$ & $S ; U ; S(\mathrm{x}) \preceq \mathrm{T}$ & (S-SoLVE-ID) \\
\hline$S ; U ; C_{1} \wedge C_{2}$ & $\rightarrow$ & $S\left[[] \wedge C_{2}\right] ; U ; C_{1}$ & (S-SolvE-And) \\
\hline$S ; U ; \exists \overline{\mathrm{X}} . C$ & $\rightarrow$ & \begin{tabular}{l}
$S[\exists \overline{\mathrm{X}} .[]] ; U ; C$ \\
if $\overline{\mathrm{x}} \# \operatorname{ftv}(U)$
\end{tabular} & (S-SOLVE-Ex) \\
\hline$S ; U ;$ let $\mathrm{x}: \forall \overline{\mathrm{x}}[D] . \mathrm{T}$ in $C$ & $\rightarrow$ & \begin{tabular}{l}
$S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}}[\mathrm{\square}] . \mathrm{T}$ in $C] ; U ; D$ \\
if $\overline{\mathrm{x}} \# \operatorname{ftv}(U)$
\end{tabular} & (S-SOLVE-LET) \\
\hline$S[\square \wedge C] ; U ;$ true & $\rightarrow$ & $S ; U ; C$ & (S-POP-AND) \\
\hline$S[$ let $\mathrm{x}: \forall \overline{\mathrm{x}}[\mathrm{[]}] \mathrm{T}$ in $C] ; U$; true & $\rightarrow$ & \begin{tabular}{l}
$S[$ let $\mathrm{x}: \forall \overline{\mathrm{x}} \mathrm{X}[[]] \mathrm{X}$ in $C]$ \\
$U \wedge \mathrm{X}=\mathrm{T} ;$ true \\
if $\mathrm{x} \notin \operatorname{ftv}(U, \mathrm{~T}) \wedge \mathrm{T} \notin \mathcal{V}$
\end{tabular} & $(\mathrm{S}-\mathrm{NAME}-2)$ \\
\hline$S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}} \mathrm{Y}[[]] . \mathrm{X}$ in $C] ; \mathrm{Y}=\mathrm{Z}=\epsilon \wedge U$; true & $\rightarrow$ & \begin{tabular}{l}
$S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}} \mathrm{Y}[[]] . \theta(\mathrm{X})$ in $C]$ \\
$\mathrm{Y} \wedge \mathrm{Z}=\theta(\epsilon) \wedge \theta(U) ;$ true \\
if $\mathrm{Y} \neq \mathrm{Z} \wedge \theta=[\mathrm{Y} \mapsto \mathrm{Z}]$
\end{tabular} & (S-COMpREss) \\
\hline$S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}} \mathrm{Y}[\mathrm{[}] . \mathrm{X}$ in $C] ; \mathrm{Y}=\epsilon \wedge U$; true & $\rightarrow$ & \begin{tabular}{l}
$S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}}[\mathrm{]}] \cdot \mathrm{X}$ in $C] ; \epsilon \wedge U$; true \\
if $\mathrm{Y} \notin \mathrm{x} \cup \operatorname{ftv}(\epsilon, U)$
\end{tabular} & (S-UnNAME) \\
\hline$S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}} \overline{\mathrm{Y}}[[]] . \mathrm{X}$ in $C] ; U ;$ true & $\rightarrow$ & \begin{tabular}{l}
$S[\exists \overline{\mathrm{Y}}$.let $\mathrm{x}: \forall \overline{\mathrm{X}}[\square] . \mathrm{X}$ in $C] ; U ;$ true \\
if $\overline{\mathrm{Y}} \# \operatorname{ftv}(C) \wedge \exists \overline{\mathrm{X}} . U$ determines $\overline{\mathrm{Y}}$
\end{tabular} & (S-LETALL) \\
\hline$S[$ let x : $\forall \overline{\mathrm{x}}[[]] . \mathrm{x}$ in $C] ; U_{1} \wedge U_{2} ;$ true & $\rightarrow$ & \begin{tabular}{l}
$S\left[\right.$ let x : $\forall \overline{\mathrm{x}}\left[U_{2}\right] \cdot \mathrm{X}$ in $\left.\square\right] ; U_{1} ; C$ \\
if $\overline{\mathrm{x}} \# \operatorname{ftv}\left(U_{1}\right) \wedge \exists \overline{\mathrm{x}} \cdot U_{2} \equiv$ true
\end{tabular} & (S-POP-LET) \\
\hline$S[$ let $\mathrm{x}: \sigma$ in []$] ; U$; true & $\rightarrow$ & $S ; U ;$ true & (S-Pop-Env) \\
\hline
\end{tabular}

Figure 1-12: A constraint solver
initially described in (Rémy, 1992a), and also appear in (McAllester, 2003).

Rules S-Solve-EQ to S-SoLVE-LET encode an analysis of the structure of the third component of the current state. There is one rule for each possible case, except false, which by assumption cannot arise, and true, which is dealt with further on. S-SolvE-EQ discovers an equation and makes it available to the unification algorithm. S-SOLVE-ID discovers an instantiation constraint $\mathrm{x} \preceq \mathrm{T}$ and replaces it with $\sigma \preceq \mathrm{T}$, where the type scheme $\sigma=S(\mathrm{x})$ is the type scheme carried by the nearest environment frame that defines $\mathrm{x}$ in the stack $S$. It is defined as follows:

$$
\begin{aligned}
& S[[] \wedge C](\mathrm{x})=S(\mathrm{x}) \\
& S[\exists \overline{\mathrm{x}} . \square](\mathrm{x})=S(\mathrm{x}) \text { if } \overline{\mathrm{x}} \# \operatorname{ftv}(S(\mathrm{x})) \\
& S[\text { let y }: \forall \overline{\mathrm{x}}[\mathrm{\square}] . \mathrm{T} \text { in } C](\mathrm{x})=S(\mathrm{x}) \text { if } \overline{\mathrm{x}} \# \operatorname{ftv}(S(\mathrm{x})) \\
& S[\text { let } \mathrm{y}: \sigma \text { in } \square](\mathrm{x})=S(\mathrm{x}) \text { if } \mathrm{x} \neq \mathrm{y} \\
& S[\text { let } \mathrm{x}: \sigma \text { in } \square](\mathrm{x})=\sigma
\end{aligned}
$$

If $\mathrm{x} \in d p i(S)$ does not hold, then $S(\mathrm{x})$ is undefined and the rule is not applicable. If it does hold, then the rule may always be made applicable by suitable $\alpha$-conversion of the left-hand state. Please recall that, if $\sigma$ is of the form $\forall \overline{\mathrm{X}}[U] . \mathrm{X}$, where $\overline{\mathrm{X}} \# \operatorname{ftv}(\mathrm{T})$, then $\sigma \preceq \mathrm{T}$ stands for $\exists \overline{\mathrm{X}} .(U \wedge \mathrm{X}=\mathrm{T})$. The process of constructing this constraint is informally referred to as "taking an instance of $\sigma$ ". It involves taking fresh copies of the type variables $\overline{\mathrm{X}}$, of the unification constraint $U$, and of the body $\mathrm{X}$. In the worst case, this process is just as inefficient as textually expanding the corresponding let construct in the program's source code, and leads to exponential time complexity (Mairson, Kanellakis, and Mitchell, 1991). In practice, however, the unification constraint $U$ is often compact, because it was simplified before the environment frame let $\mathrm{x}: \sigma$ in [] was created. which is why the solver usually performs well. (The creation of environment frames, performed by S-POP-LET, is discussed below.) S-SOLVEAND discovers a conjunction. It arbitrarily chooses to explore the left branch first, and pushes a conjunction frame onto the stack, so as to record that the right branch should be explored afterwards. S-SOLVE-Ex discovers an existential quantifier and enters it, creating a new existential frame to record its existence. Similarly, S-SOLVE-LET discovers a let form and enters its left-hand side, creating a new let frame to record its existence. The choice of examining the left-hand side first is not arbitrary. Indeed, examining the right-hand side first would require creating an environment frame-but environment frames must contain simplified type schemes of the form $\forall \overline{\mathrm{X}}[U] . \mathrm{X}$, whereas the type scheme $\forall \overline{\mathrm{X}}[D] . T$ is arbitrary. In other words, our strategy is to simplify type schemes prior to allowing them to be copied by S-SOLVE-ID, so as to avoid any duplication of effort. The side-conditions of S-SOLVE-Ex and S-SOLVE-LET may always be satisfied by suitable $\alpha$-conversion of the left-hand state.

Rules S-Solve-EQ to S-Solve-LEt may be referred to as forward rules, because they "move down into" the external constraint, causing the stack to grow. This process stops when the external constraint at hand becomes true. Then, part of the work has been finished, and the solver must examine the stack in order to determine what to do next. This task is performed by the last series of rules, which may be referred to as backward rules, because they "move back out", causing the stack to shrink, and possibly scheduling new external constraints for examination. These rules encode an analysis of the structure of the innermost stack frame. There are three cases, corresponding to conjunction, let, and environment frames. The case of existential stack frames need not be considered, because rules S-Ex-2 to S-Ex-4 allow either fusing them with let frames or floating them up to the outermost level, where they shall remain inert. S-POP-And deals with conjunction frames. The frame is popped, and the external constraint that it carries is scheduled for examination. S-Pop-Env deals with environment frames. Because the right-hand side of the let construct at hand has been solved - that is, turned into a unification constraint $U$-it cannot contain an occurrence of $\mathrm{x}$. Furthermore, by assumption, $\exists \sigma$ is true. Thus, this environment frame is no longer useful: it is destroyed. The remaining rules deal with let frames. Roughly speaking, their purpose is to change the state $S[$ let $\mathrm{x}: \forall \overline{\mathrm{x}}[[]] . T$ in $C] ; U$; true into $S[$ let $\mathrm{x}: \forall \overline{\mathrm{x}}[U] . T$ in []$]$; true; $C$, that is, to turn the current unification constraint $U$ into a type scheme, turn the let frame into an environment frame, and schedule the right-hand side of the let construct (that is, the external constraint $C$ ) for examination. In fact, the process is more complex, because the type scheme $\forall \overline{\mathrm{X}}[U]$.T must be simplified before becoming part of an environment frame. The simplification process is described by rules S-NAME-2 to S-Pop-LET. In the following, we refer to type variables in $\overline{\mathrm{X}}$ as young and to type variables in $d t v(S) \backslash \overline{\mathrm{X}}$ as old. The former are the universal quantifiers of the type scheme that is being created; the latter are its free type variables.

S-NAME-2 ensures that the body $T$ of the type scheme that is being created is a type variable, as opposed to an arbitrary term. If it isn't, then it is replaced with a fresh variable $\mathrm{X}$, and the equation $\mathrm{X}=\mathrm{T}$ is added so as to recall that $\mathrm{X}$ stands for $\mathrm{T}$. Thus, the rule moves the term $\mathrm{T}$ into the current unification problem, where it potentially becomes subject to S-NAME-1. This ensures that sharing is made explicit everywhere. S-COMPRESS determines that the (young) type variable $\mathrm{Y}$ is an alias for the type variable $\mathrm{Z}$. Then, every free occurrence of Y other than its defining occurrence is replaced with Z. In an actual implementation, this occurs transparently when the union-find algorithm performs path compression (Tarjan, 1975, 1979), provided we are careful never to create a link from a variable to a variable of higher rank. This requires making the unification algorithm aware of ranks, but is otherwise
easily achieved. S-UNNAME determines that the (young) type variable Y has no occurrences other than its defining occurrence in the current type scheme. (This occurs, in particular, when S-Compress has just been applied.) Then, $\mathrm{Y}$ is suppressed altogether. In the particular case where the remaining multiequation $\epsilon$ has cardinal 1, it may then be suppressed by S-SingLE. In other words, the combination of S-UNNAME and S-SINGLE is able to suppress young unused type variables as well as the term that they stand for. This may, in turn, cause new type variables to become eligible for elimination by $\mathrm{S}$ UNNAME. In fact, assuming the current unification constraint is acyclic, an inductive argument shows that every young type variable may be suppressed unless it is dominated either by $\mathrm{X}$ or by an old type variable. (In the setting of a regular tree model, it is possible to extend the rule so that young cycles that are not dominated either by $\mathrm{X}$ or by an old type variable are suppressed as well.) S-LETALL is a directed version of C-LETALL. It turns the young type variables $\overline{\mathrm{Y}}$ into old variables. How to tell whether $\exists \overline{\mathrm{X}} . U$ determines $\overline{\mathrm{Y}}$ is discussed later (see Lemma 1.8.7). Why S-LETALL is an interesting and important rule will be explained shortly. S-POP-LET is meant to be applied when the current state has become a normal form with respect to S-UNIFY, SName-2, S-Compress, S-UnName, and S-LetAll, that is, when the type scheme that is about to be created is fully simplified. It splits the current unification constraint into two components $U_{1}$ and $U_{2}$, where $U_{1}$ is made up entirely of old variables - as expressed by the side-condition $\overline{\mathrm{X}} \# \operatorname{ftv}\left(U_{1}\right)$ and $U_{2}$ constrains young variables only-as expressed by the side-condition $\exists \overline{\mathrm{X}} \cdot U_{2} \equiv$ true. Please note that $U_{2}$ may still contain free occurrences of old type variables, so the type scheme $\forall \overline{\mathrm{X}}\left[U_{2}\right]$. $\mathrm{X}$ that appears on the right-hand side is not necessarily closed. It is not obvious why such a decomposition must exist; the proof of Lemma 1.8.11 sheds more light on this issue. Let us say, for now, that S-LETALL plays a role in guaranteeing its existence, whence part of its importance. Once the decomposition $U_{1} \wedge U_{2}$ is obtained, the behavior of $\mathrm{S}$ POP-LET is simple. The unification constraint $U_{1}$ concerns old variables only, that is, variables that are not quantified in the current let frame; thus, it need not become part of the new type scheme, and may instead remain part of the current unification constraint. This is justified by C-LETAnd and C-InAnd* (see the proof of Lemma 1.8.10) and corresponds to the difference between HMX-GEN' and HMX-GEN discussed in Section 1.4. The unification constraint $U_{2}$, on the other hand, becomes part of the newly built type scheme $\forall \overline{\mathrm{X}}\left[U_{2}\right]$.X. The property $\exists \overline{\mathrm{X}} . U_{2} \equiv$ true guarantees that the newly created environment frame meets the requirements imposed on such frames. Please note that, the more type variables are considered old, the larger $U_{1}$ may become, and the smaller $U_{2}$. This is another reason why S-LETALL is interesting: by allowing more variables to be considered old, it decreases the size of the type scheme
$\forall \overline{\mathrm{X}}\left[U_{2}\right] . \mathrm{X}$, making it cheaper to take instances of.

To complete our description of the constraint solver, there remains to explain how to decide when $\exists \overline{\mathrm{X}} . U$ determines $\overline{\mathrm{Y}}$, since this predicate occurs in the side-condition of S-LETALL. The following lemma describes two important situations where, by examining the structure of an equation, it is possible to discover that a constraint $C$ determines some of its free type variables $\bar{Y}$ (Definition 1.3.26). In the first situation, the type variables $\overline{\mathrm{Y}}$ are equated with or dominated by a distinct type variable X that occurs free in $C$. In that case, because the model is a free tree model, the values of the type variables $\bar{Y}$ are determined by the value of $X$ - they are subtrees of it at specific positions. For instance, $\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}$ determines $\mathrm{Y}_{1} \mathrm{Y}_{2}$, while $\exists \mathrm{Y}_{1} .\left(\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}\right)$ determines $\mathrm{Y}_{2}$. In the second situation, the type variables $\overline{\mathrm{Y}}$ are equated with a term T, all of whose free type variables are free in $C$. Again, the value of the type variables $\overline{\mathrm{Y}}$ is then determined by the values of the type variables $f t v(T)$-indeed, the term $\mathrm{T}$ itself defines a function that maps the latter to the former. For instance, $\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}$ determines $\mathrm{X}$, while $\exists \mathrm{Y}_{1}$. $\left(\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}\right)$ does not. In the second situation, no assumption is in fact made about the model. Please note that $\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}$ determines $\mathrm{Y}_{1} \mathrm{Y}_{2}$ and determines $\mathrm{X}$, but does not simultaneously determine $\mathrm{XY}_{1} \mathrm{Y}_{2}$.

1.8.7 Lemma: Let $\overline{\mathrm{X}} \# \overline{\mathrm{Y}}$. Assume either $\epsilon$ is $\mathrm{X}=\epsilon^{\prime}$, where $\mathrm{X} \notin \overline{\mathrm{X}} \overline{\mathrm{Y}}$ and $\overline{\mathrm{Y}} \subseteq f t v\left(\epsilon^{\prime}\right)$, or $\epsilon$ is $\overline{\mathrm{Y}}=\mathrm{T}=\epsilon^{\prime}$, where $\operatorname{ftv}(\mathrm{T}) \# \overline{\mathrm{X}} \overline{\mathrm{Y}}$. Then, $\exists \overline{\mathrm{X}}$. $(C \wedge \epsilon)$ determines $\overline{\mathrm{Y}}$.

Proof: Let $\overline{\mathrm{X}} \# \overline{\mathrm{Y}}$ (1). Let $\phi \vdash \operatorname{def} \Gamma$ in $\exists \overline{\mathrm{X}}$. $(C \wedge \epsilon)$ (2) and $\phi^{\prime} \vdash$ def $\Gamma$ in $\exists \overline{\mathrm{X}}$. $(C \wedge \epsilon)(3)$, where $\phi$ and $\phi^{\prime}$ coincide outside of $\overline{\mathrm{Y}}$. We may assume, w.l.o.g., $\overline{\mathrm{x}} \# \mathrm{ftv}(\Gamma)$ (4). By (2), (4), CM-Exists, and CM-And, we obtain $\phi_{1} \vdash \operatorname{def} \Gamma$ in $\epsilon(5)$, where $\phi$ and $\phi_{1}$ coincide outside $\overline{\mathrm{x}}$. By CM-Predicate, (5) implies that all members of $\epsilon$ have the same image through $\phi_{1}$. Similarly, exploiting (3) and (4), we find that all members of $\epsilon$ have the same image through $\phi_{1}^{\prime}$, where $\phi^{\prime}$ and $\phi_{1}^{\prime}$ coincide outside $\overline{\mathrm{X}}$. Now, we claim that $\phi_{1}$ and $\phi_{1}^{\prime}$ coincide on $\overline{\mathrm{Y}}$. Once the claim is established, by (1), there follows that $\phi$ and $\phi^{\prime}$ must coincide on $\bar{Y}$ as well, which is the goal. So, there only remains to establish the claim; we distinguish two subcases.

Subcase $\epsilon$ is $\mathrm{X}=\epsilon^{\prime}$ and $\mathrm{X} \notin \overline{\mathrm{X}} \overline{\mathrm{Y}}(\mathbf{6})$ and $\overline{\mathrm{Y}} \subseteq f t v\left(\epsilon^{\prime}\right)$ (7). Because $\phi_{1}$ and $\phi_{1}^{\prime}$ coincide outside $\overline{\mathrm{X}} \overline{\mathrm{Y}}$ and by (6), we have $\phi_{1}(\mathrm{X})=\phi_{1}^{\prime}(\mathrm{X})$. As a result, all members of $\epsilon^{\prime}$ have the same image through $\phi_{1}$ and $\phi_{1}^{\prime}$. In a free tree model, where decomposition is valid, a simple inductive argument shows that $\phi_{1}$ and $\phi_{1}^{\prime}$ must coincide on $f t v\left(\epsilon^{\prime}\right)$, hence - by (7) - also on $\overline{\mathrm{Y}}$.

Subcase $\epsilon$ is $\overline{\mathrm{Y}}=\mathrm{T}=\epsilon^{\prime}$ and $f t v(\mathrm{~T}) \# \overline{\mathrm{X}} \overline{\mathrm{Y}}(8)$. Because $\phi_{1}$ and $\phi_{1}^{\prime}$ coincide outside $\bar{X} \bar{Y}$ and by (8), we have $\phi_{1}(T)=\phi_{1}^{\prime}(T)$. Thus, for every $Y \in \bar{Y}$, we have $\phi_{1}(\mathrm{Y})=\phi_{1}(\mathrm{~T})=\phi_{1}^{\prime}(\mathrm{T})=\phi_{1}^{\prime}(\mathrm{Y})$. That is, $\phi_{1}$ and $\phi_{1}^{\prime}$ coincide on $\overline{\mathrm{Y}}$.

Thanks to Lemma 1.8.7, a straightforward implementation of S-LETALL
comes to mind. The problem is, given a constraint $\exists \overline{\mathrm{X}} . U$, where $U$ is a standard conjunction of multi-equations, to determine the greatest subset $\bar{Y}$ of $\bar{X}$ such that $\exists(\overline{\mathrm{X}} \backslash \overline{\mathrm{Y}}) . U$ determines $\overline{\mathrm{Y}}$. By the first part of the lemma, it is safe for $\overline{\mathrm{Y}}$ to include all members of $\overline{\mathrm{X}}$ that are directly or indirectly dominated (with respect to $U$ ) by some free variable of $\exists \overline{\mathrm{x}} . U$. Those can be found, in time linear in the size of $U$, by a top-down traversal of the graph of $\prec_{U}$. By the second part of the lemma, it is safe to close $\overline{\mathrm{Y}}$ under the closure law $\mathrm{X} \in$ $\overline{\mathrm{X}} \wedge\left(\forall \mathrm{Y} \quad \mathrm{Y} \prec_{U} \mathrm{X} \Rightarrow \mathrm{Y} \in \overline{\mathrm{Y}}\right) \Rightarrow \mathrm{X} \in \overline{\mathrm{Y}}$. That is, it is safe to also include all members of $\overline{\mathrm{X}}$ whose descendants (with respect to $U$ ) have already been found to be members of $\bar{Y}$. This closure computation may be performed, again in linear time, by a bottom-up traversal of the graph of $\prec_{U}$. When $U$ is acyclic, it is possible to show that this procedure is complete, that is, does compute the greatest subset $\bar{Y}$ that meets our requirement. This is the topic of the following exercise.

1.8.8 EXERcise $[\star \star \star, \nrightarrow]$ : Assuming $U$ is acyclic, prove that the above procedure computes the greatest subset $\overline{\mathrm{Y}}$ of $\overline{\mathrm{X}}$ such that $\exists(\overline{\mathrm{X}} \backslash \overline{\mathrm{Y}}) \cdot U$ determines $\overline{\mathrm{Y}}$. In the setting of a regular tree model, exhibit a satisfiable constraint $U$ such that the above procedure is incomplete. Can you define a complete procedure in that setting?

The above discussion has shown that when $\mathrm{Y}$ and $\mathrm{Z}$ are equated, if $\mathrm{Y}$ is young and $\mathrm{Z}$ is old, then $\mathrm{S}$-LetAlL allows making $\mathrm{Y}$ old as well. If binding information is encoded in terms of integer ranks, as suggested earlier, then this remark may be formulated as follows: when $\mathrm{Y}$ and $\mathrm{Z}$ are equated, if the rank of $Y$ exceeds that of $Z$, then it may be decreased so that both ranks match. As a result, it is possible to attach ranks with multi-equations, rather than with variables. When two multi-equations are fused, the smaller rank is kept.

S-SOLVE-LET and S-NAME-2 to S-POP-LET are unnecessarily complex when $\mathrm{x}$ is assigned a monotype $\mathrm{T}$, rather than an arbitrary type scheme $\forall \overline{\mathrm{X}}[D]$.T. In that case, the combined effect of these rules may be obtained directly via the following two new rules, which may be implemented in a more efficient way:

$$
\begin{array}{rll}
S ; U ; \text { let } \mathrm{x}: \mathrm{T} \text { in } C \rightarrow & S[\exists \mathrm{x} .[]] ; U \wedge \mathrm{x}=\mathrm{T} \text {; let } \mathrm{x}: \mathrm{x} \text { in } C \\
& & \text { if } \mathrm{x} \notin f t v(U, \mathrm{~T}, C) \wedge \mathrm{T} \notin \mathcal{V} \\
& & \\
S ; U ; \text { let } \mathrm{x}: \mathrm{x} \text { in } C \rightarrow & & S[\text { let } \mathrm{x}: \mathrm{x} \text { in }[]] ; U ; C \quad \text { (S-Solve-LET-Mono) }
\end{array}
$$

If $\mathrm{T}$ isn't a variable, it is replaced with a fresh variable $\mathrm{X}$, together with the equation $\mathrm{X}=\mathrm{T}$. This corresponds to the effect of S-NAME-2. Then, we directly
create an environment frame for $\mathrm{x}$, without bothering to create and discard a let frame, since there is no way the type scheme X may be further simplified.

Let us now state and establish the properties of the constraint solver. First, the reduction system is terminating, so it defines an algorithm.

1.8.9 Lemma: The reduction system $\rightarrow$ is strongly normalizing.

Second, every rewriting step preserves the meaning of the constraint that the current state represents. We recall that the state $S ; U ; C$ is meant to represent the constraint $S[U \wedge C]$.

1.8.10 Lemma: $S ; U ; C \rightarrow S^{\prime} ; U^{\prime} ; C^{\prime}$ implies $S[U \wedge C] \equiv S^{\prime}\left[U^{\prime} \wedge C^{\prime}\right]$.

Proof: By examination of every rule.
- Case S-Unify. By Lemma 1.8.5.
- Case S-Ex-1, S-Ex-2, S-Solve-Ex. By C-ExAnd.
- Case S-Ex-3. By C-LETEx.
- Case S-Ex-4. By C-InEx.
- Case S-Solve-Eq, S-Pop-And. By C-Dup.
- Case S-Solve-ID. Because $\sigma$ is of the form $\forall \overline{\mathrm{x}}[U] . \mathrm{X}$, we have $f p i(\sigma)=\varnothing$. The result follows by C-INID.
- Case S-Solve-And. By C-AndAnd.
- Case S-Solve-Let. By C-LetAnd.
- Case S-NAme-2. By Definition 1.3.21 and C-NAmeEq, $\mathrm{X} \notin f t v(U, \mathrm{~T}) \mathrm{im}-$ plies true $\Vdash \forall \overline{\mathrm{X}}[U] . \mathrm{T} \equiv \forall \overline{\mathrm{X}} \mathrm{X}[U \wedge \mathrm{X}=\mathrm{T}] . \mathrm{X}$. The result follows by Lemma 1.3.22.
- Case S-Compress. Let $\theta=[\mathrm{Y} \mapsto \mathrm{Z}]$. By Definition 1.3.21 and CNAMEEQ, $\mathrm{Y} \neq \mathrm{Z}$ implies true $\Vdash \forall \overline{\mathrm{X}}[\mathrm{Y}=\mathrm{Z}=\epsilon \wedge U] . \mathrm{X} \equiv \forall \overline{\mathrm{X}} \mathrm{Y}[\mathrm{Y} \wedge \mathrm{Z}=$ $\theta(\epsilon) \wedge \theta(U)] . \theta(\mathrm{X})$. The result follows by Lemma 1.3.22.
- Case S-UnName. Using Lemma 1.3.18, it is straightforward to check that $\mathrm{Y} \notin f t v(\epsilon)$ implies $\exists \mathrm{Y}$. $(\mathrm{Y}=\epsilon) \equiv \epsilon$. The result follows by C-ExAnD and C-LETEx.
- Case S-LetAll. By C-LetAll.
- Case S-Pop-Let. By C-LetAnd and C-InAnd*.
- Case S-Pop-Env. By C-IN*, recalling that $\exists \sigma$ must be true.

Last, we classify the normal forms of the reduction system:

1.8.11 Lemma: A normal form for the reduction system $\rightarrow$ is one of (i) $S ; U ; \mathrm{x} \preceq \mathrm{T}$, where $\mathrm{x} \notin d p i(S)$; (ii) $S$; false; true; or (iii) $\mathcal{X}$; $U$; true, where $\mathcal{X}$ is an existential constraint context and $U$ a satisfiable conjunction of multi-equations.

Proof: Because, by definition, $S ; U$; false is not a valid state, a normal form for S-Solve-Eq, S-Solve-Id, S-Solve-And, S-Solve-Ex, and S-SolveLET must be either an instance of the left-hand side of S-SOLVE-ID, with $\mathrm{x} \notin d p i(S)$, which corresponds to case (i), or of the form $S$; $U$; true. Let us consider the latter case. Because $S ; U$; true is a normal form with respect to S-UNIFY, by Lemma 1.8.6, $U$ must be either false of the form $\mathcal{X}\left[U^{\prime}\right]$, where $U^{\prime}$ is a standard conjunction of multi-equations and, if the model is syntactic, $U^{\prime}$ is acyclic. The former case corresponds to (ii); thus, let us consider the latter case. Because $S ; \mathcal{X}\left[U^{\prime}\right]$; true is a normal form with respect to $\mathrm{S}$-EX1 , the context $\mathcal{X}$ must in fact be empty, and $U^{\prime}$ is $U$. If $S$ is an existential constraint context, then we are in situation (iii). Otherwise, because $S ; U$; true is a normal form with respect to S-Ex-2, S-Ex-3, and S-Ex-4, the stack $S$ does not end with an existential frame. Because $S ; U$; true is a normal form with respect to S-Pop-And and S-Pop-Env, $S$ must then be of the form $S^{\prime}[$ let $\mathrm{x}: \forall \overline{\mathrm{X}}[\mathrm{[I}] \mathrm{T}$ in $C]$. Because $S ; U$; true is a normal form with respect to S-NAME-2, T must be a type variable $\mathrm{X}$. Let us write $U$ as $U_{1} \wedge U_{2}$, where $\overline{\mathrm{X}} \# \operatorname{ftv}\left(U_{1}\right)$, and where $U_{1}$ is maximal for this criterion. Then, consider a multi-equation $\epsilon \in U$. By the first part of Lemma 1.8.7, if one variable member of $\epsilon$ is free (that is, outside $\overline{\mathrm{X}}$ ), then $\exists \overline{\mathrm{X}} . U$ determines all other variables in $f t v(\epsilon)$. Because $S ; U$; true is a normal form with respect to S-LETALL, all variables in $f t v(\epsilon)$ must then be free (that is, outside $\overline{\mathrm{X}}$ ). By definition of $U_{1}$, this implies $\epsilon \in U_{1}$. By contraposition, for every multi-equation $\epsilon \in U_{2}$, all variable members of $\epsilon$ are in $\overline{\mathrm{X}}$. Furthermore, let us recall that $U_{2}$ is a standard conjunction of multi-equations and, if the model is syntactic, $U_{2}$ is acyclic. We let the reader check that this implies $\exists \overline{\mathrm{x}} . U_{2} \equiv$ true; the proof is a slight generalization of the last part of that of Lemma 1.8.6. Then, $S ; U$; true is reducible via S-PoP-LET. This is a contradiction, so this last case cannot arise.

In case (i), the constraint $S[U \wedge C]$ has a free program identifier x, so it is not satisfiable. In other words, the source program contains an unbound program identifier. Such an error could of course be detected prior to constraint solving, if desired. In case (ii), the unification algorithm failed. By Lemma 1.3.30, the constraint $S[U \wedge C]$ is then false. In case (iii), the constraint $S[U \wedge C]$ is equivalent to $\mathcal{X}[U]$, where $U$ is satisfiable, so it is satisfiable as well. Thus, each of the three classes of normal forms may be immediately identified as denoting success or failure. Thus, Lemmas 1.8.10 and 1.8.11 indeed prove that the algorithm is a constraint solver.

\subsection*{1.9 From ML-the-calculus to ML-the-programming-language}

In this section, we explain how to extend the framework developed so far to accommodate operations on values of base type (such as integers), pairs, sums, references, and recursive function definitions. Then, we describe more complex extensions, namely algebraic data type definitions, pattern matching, and type annotations. Last, the issues associated with recursive types are briefly discussed. Exceptions are not discussed; the reader is referred to (TAPL Chapter 14).

\section*{Simple extensions}

Many features of ML-the-programming-language may be introduced into MLthe-calculus by introducing new constants and extending $\xrightarrow{\delta}$ and $\Gamma_{0}$ appropriately. In each case, it is necessary to check that the requirements of Definition 1.7 .6 are met, that is, the new initial environment faithfully reflects the nature of the new constants as well as the behavior of the new reduction rules. Below, we describe several such extensions in isolation.

1.9.1 Exercise [Integers, Recommended, $\star \star$ ]: Integer literals and integer addition have been introduced and given an operational semantics in Examples 1.2.1, 1.2.2 and 1.2.4. Let us now introduce an isolated type constructor int of signature $\star$ and extend the initial environment $\Gamma_{0}$ with the bindings $\hat{n}$ : int, for every integer $n$, and $\hat{+}:$ int $\rightarrow$ int $\rightarrow$ int. Check that these definitions meet the requirements of Definition 1.7.6.

1.9.2 Exercise [Booleans, Recommended, $\star \star, \nrightarrow$ ]: Booleans and conditionals have been introduced and given an operational semantics in Exercise 1.2.6. Introduce an isolated type constructor bool to represent Boolean values and explain how to extend the initial environment. Check that your definitions meet the requirements of Definition 1.7.6. What is the constraint generation rule for the syntactic sugar if $t_{0}$ then $t_{1}$ else $t_{2}$ ?

1.9.3 ExERcISE [PaIrs, $\star \star, \nrightarrow]$ : Pairs and pair projections have been introduced and given an operational semantics in Examples 1.2.3 and 1.2.5. Let us now introduce an isolated type constructor $\times$ of signature $\star \otimes \star \Rightarrow \star$, covariant in both of its parameters, and extend the initial environment $\Gamma_{0}$ with the following bindings:

$$
\begin{aligned}
(\cdot, \cdot): & \forall \mathrm{XY} . \mathrm{X} \rightarrow \mathrm{Y} \rightarrow \mathrm{X} \times \mathrm{Y} \\
\pi_{1}: & \forall \mathrm{XY} . \mathrm{X} \times \mathrm{Y} \rightarrow \mathrm{X} \\
\pi_{2}: & \forall \mathrm{XY} . \mathrm{X} \times \mathrm{Y} \rightarrow \mathrm{Y}
\end{aligned}
$$

Check that these definitions meet the requirements of Definition 1.7.6.

1.9.4 ExERcise [Sums, $\star \star, \nrightarrow$ ]: Sums have been introduced and given an operational semantics in Example 1.2.7. Let us now introduce an isolated type constructor + of signature $\star \otimes \star \Rightarrow \star$, covariant in both of its parameters, and extend the initial environment $\Gamma_{0}$ with the following bindings:

$$
\begin{aligned}
\operatorname{inj}_{1}: & \forall X Y . X \rightarrow \mathrm{X}+\mathrm{Y} \\
\mathrm{inj}_{2}: & \forall \mathrm{XY.Y} \rightarrow \mathrm{X}+\mathrm{Y} \\
\text { case }: & \forall \mathrm{XYZ} .(\mathrm{X}+\mathrm{Y}) \rightarrow(\mathrm{X} \rightarrow \mathrm{Z}) \rightarrow(\mathrm{Y} \rightarrow \mathrm{Z}) \rightarrow \mathrm{Z}
\end{aligned}
$$

Check that these definitions meet the requirements of Definition 1.7.6.

1.9.5 EXERcise [REfEREnces, $\star \star \star$ ]: References have been introduced and given an operational semantics in Example 1.2.9. The type constructor ref has been introduced in Definition 1.7.4. Let us now extend the initial environment $\Gamma_{0}$ with the following bindings:

$$
\begin{aligned}
\text { ref }: & \forall X . X \rightarrow \operatorname{ref} X \\
!: & \forall X . \operatorname{ref} X \rightarrow X \\
:=: & \forall X . \operatorname{ref} X \rightarrow X \rightarrow X
\end{aligned}
$$

Check that these definitions meet the requirements of Definition 1.7.6.

1.9.6 Exercise [Recursion, Recommended, $\star \star \star$ ]: The fixpoint combinator fix has been introduced and given an operational semantics in Example 1.2.10. Let us now extend the initial environment $\Gamma_{0}$ with the following binding:

$$
\text { fix : } \quad \forall X Y .((X \rightarrow Y) \rightarrow(X \rightarrow Y)) \rightarrow X \rightarrow Y
$$

Check that these definitions meet the requirements of Definition 1.7.6. Recall how the letrec syntactic sugar was defined in Example 1.2.10, and check that this gives rise to the following constraint generation rule:

$$
\begin{aligned}
& \text { let } \Gamma_{0} \text { in } \llbracket \text { letrec } f=\lambda z . \mathrm{t}_{1} \text { in } \mathrm{t}_{2}: \mathrm{T} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in let } \mathrm{f}: \forall \mathrm{XY}\left[\text { let } \mathrm{f}: \mathrm{X} \rightarrow \mathrm{Y} ; \mathrm{z}: \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{Y} \rrbracket\right] \mathrm{X} \rightarrow \mathrm{Y} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket
\end{aligned}
$$

Note the somewhat peculiar structure of this constraint: the program variable $f$ is bound twice in it, with different type schemes. The constraint requires all occurrences of $f$ within $t_{1}$ to be assigned the monomorphic type $\mathrm{X} \rightarrow \mathrm{Y}$. This type is generalized and turned into a type scheme before inspecting $t_{2}$, however, so every occurrence of $f$ within $t_{2}$ may receive a different type, as usual with let-polymorphism. A more powerful way of typechecking recursive function definitions is discussed in Section 1.10 (page 113).

\section*{Algebraic data types}

Exercises 1.9.3 and 1.9.4 have shown how to extend the language with binary, anonymous products and sums. These constructs are quite general, but still have several shortcomings. First, they are only binary, while we would like to have $k$-ary products and sums, for arbitrary $k \geq 0$. Such a generalization is of course straightforward. Second, more interestingly, their components must be referred to by numeric index (as in "please extract the second component of the pair"), rather than by name ("extract the component named y"). In practice, it is crucial to use names, because they make programs more readable and more robust in the face of changes. One could introduce a mechanism that allows defining names as syntactic sugar for numeric indices. That would help a little, but not much, because these names would not appear in types, which would still be made of anonymous products and sums. Third, in the absence of recursive types, products and sums do not have sufficient expressiveness to allow defining unbounded data structures, such as lists. Indeed, it is easy to see that every value whose type $\mathrm{T}$ is composed of base types (int, bool, etc.), products, and sums must have bounded size, where the bound $|\mathrm{T}|$ is a function of T. More precisely, up to a constant factor, we have $\mid$ int $|=|$ bool $\mid=1$, $\left|\mathrm{T}_{1} \times \mathrm{T}_{2}\right|=1+\left|\mathrm{T}_{1}\right|+\left|\mathrm{T}_{2}\right|$, and $\left|\mathrm{T}_{1}+\mathrm{T}_{2}\right|=1+\max \left(\left|\mathrm{T}_{1}\right|,\left|\mathrm{T}_{2}\right|\right)$. The following example describes another facet of the same problem.

1.9.7 Example: A list is either empty, or a pair of an element and another list. So, it seems natural to try and encode the type of lists as a sum of some arbitrary type (say, unit), on the one hand, and of a product of some element type and of the type of lists itself, on the other hand. With this encoding in mind, we can go ahead and write code - for instance, a function that computes the length of a list:

$$
\text { letrec length }=\lambda \text { l.case } 1\left(\lambda_{-} . \hat{0}\right)\left(\lambda z . \hat{1} \hat{+} \text { length }\left(\pi_{2} z\right)\right)
$$

We have used integers, pairs, sums, and the letrec construct introduced in the previous section. The code analyzes the list 1 using a case construct. If the left branch is taken, the list is empty, so 0 is returned. If the right branch is taken, then $z$ becomes bound to a pair of some element and the tail of the list. The latter is obtained using the projection operator $\pi_{2}$. Its length is computed using a recursive call to length and incremented by 1 . This code makes perfect sense. However, applying the constraint generation and constraint solving algorithms eventually leads to an equation of the form $\mathrm{X}=\mathrm{Y}+(\mathrm{Z} \times \mathrm{X})$, where $\mathrm{X}$ stands for the type of 1 . This equation accurately reflects our encoding of the type of lists. However, in a syntactic model, it has no solution, so our definition of length is ill-typed. It is possible to adopt a free
regular tree model,thus introducing equirecursive types into the system (TAPL Chapter 20); however, there are good reasons not to do so (page 106).

To work around this problem, ML-the-programming-language offers algebraic data type definitions, whose elegance lies in the fact that, while representing only a modest theoretical extension, they do solve the three problems mentioned above. An algebraic data type may be viewed as an abstract type that is declared to be isomorphic to a ( $k$-ary) product or sum type with named components. The type of each component is declared as well, and may refer to the algebraic data type that is being defined: thus, algebraic data types are isorecursive (TAPL Chapter 20). In order to allow sufficient flexibility when declaring the type of each component, algebraic data type definitions may be parameterized by a number of type variables. Last, in order to allow the description of complex data structures, it is necessary to allow several algebraic data types to be defined at once; the definitions may then be mutually recursive. In fact, in order to simplify this formal presentation, we assume that all algebraic data types are defined at once at the beginning of the program. This decision is of course at odds with modular programming, but will not otherwise be a problem.

In the following, D ranges over a set of data types. We assume that data types form a subset of type constructors. We require each of them to be isolated and to have a signature of the form $\vec{\kappa} \Rightarrow \star$. Furthermore, $\ell$ ranges over a set $\mathcal{L}$ of labels, which we use indifferently as data constructors and as record labels. An algebraic data type definition is either a variant type definition or a record type definition, whose respective forms are

$$
\mathrm{D} \overrightarrow{\mathrm{X}} \approx \sum_{i=1}^{k} \ell_{i}: \mathrm{T}_{i} \quad \text { and } \quad \mathrm{D} \overrightarrow{\mathrm{X}} \approx \prod_{i=1}^{k} \ell_{i}: \mathrm{T}_{i}
$$

In either case, $k$ must be nonnegative. If $\mathrm{D}$ has signature $\vec{\kappa} \Rightarrow \star$, then the type variables $\overrightarrow{\mathrm{X}}$ must have kind $\vec{\kappa}$. Every $\mathrm{T}_{i}$ must have kind $\star$. We refer to $\overline{\mathrm{X}}$ as the parameters and to $\overrightarrow{\mathrm{T}}$ (the vector formed by $\mathrm{T}_{1}, \ldots, \mathrm{T}_{k}$ ) as the components of the definition. The parameters are bound within the components, and the definition must be closed, that is, $f t v(\overrightarrow{\mathrm{T}}) \subseteq \overline{\mathrm{x}}$ must hold. Last, for an algebraic data type definition to be valid, the behavior of the type constructor $\mathrm{D}$ with respect to subtyping must match its definition. This requirement is clarified below.

1.9.8 Definition: Consider an algebraic data type definition whose parameters and components are respectively $\vec{X}$ and $\vec{T}$. Let $\vec{X}^{\prime}$ and $\vec{T}^{\prime}$ be their images under an arbitrary renaming. Then, $\mathrm{D} \overrightarrow{\mathrm{X}} \leq \mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \Vdash \overrightarrow{\mathrm{T}} \leq \overrightarrow{\mathrm{T}}^{\prime}$ must hold.

The above requirement bears on the definition of subtyping in the model. The idea is, since $\mathrm{D} \overrightarrow{\mathrm{X}}$ is declared to be isomorphic to (a sum or a product of)
$\overrightarrow{\mathrm{T}}$, whenever two types built with $\mathrm{D}$ are comparable, their unfoldings should be comparable as well. The reverse entailment assertion is not required for type soundness, and it is sometimes useful to declare algebraic data types that do not validate it-so-called phantom types (Fluet and Pucella, 2002). Note that the requirement may always be satisfied by making the type constructor $\mathrm{D}$ invariant in all of its parameters. Indeed, in that case, $D \vec{X} \leq D \vec{X}^{\prime}$ entails $\vec{X}=\vec{X}^{\prime}$, which must entail $\overrightarrow{\mathrm{T}}=\overrightarrow{\mathrm{T}}^{\prime}$ since $\overrightarrow{\mathrm{T}}^{\prime}$ is precisely $\left[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{X}^{\prime}}\right] \overrightarrow{\mathrm{T}}$. In an equality free tree model, every type constructor is naturally invariant, so the requirement is trivially satisfied. In other settings, however, it is often possible to satisfy the requirement of Definition 1.9 .8 while assigning $\mathrm{D}$ a less restrictive variance. The following example illustrates such a case.

1.9.9 Example: Let list be a data type of signature $\star \Rightarrow \star$. Let Nil and Cons be data constructors. Then, the following is a definition of list as a variant type:

$$
\text { list } \mathrm{X} \approx \Sigma(\mathrm{Nil}: \text { unit; Cons }: \mathrm{X} \times \text { list } \mathrm{X})
$$

Because data types form a subset of type constructors, it is valid to form the type list $\mathrm{X}$ in the right-hand side of the definition, even though we are still in the process of defining the meaning of list. In other words, data type definitions may be recursive. However, because $\approx$ is not interpreted as equality, the type list $\mathrm{X}$ is not a recursive type: it is nothing but an application of the unary type constructor list to the type variable $\mathrm{X}$. To check that the definition of list satisfies the requirement of Definition 1.9.8, we must ensure that

$$
\text { list } \mathrm{X} \leq \text { list } \mathrm{X}^{\prime} \Vdash \text { unit } \leq \text { unit } \wedge \mathrm{X} \times \text { list } \mathrm{X} \leq \mathrm{X}^{\prime} \times \text { list } \mathrm{X}^{\prime}
$$

holds. This assertion is equivalent to list $\mathrm{X} \leq$ list $\mathrm{X}^{\prime} \Vdash \mathrm{X} \leq \mathrm{X}^{\prime}$. To satisfy the requirement, it is sufficient to make list a covariant type constructor, that is, to define subtyping in the model so that list $\mathrm{X} \leq$ list $\mathrm{X}^{\prime} \equiv \mathrm{X} \leq \mathrm{X}^{\prime}$ holds.

Let tree be a data type of signature $\star \Rightarrow \star$. Let root and sons be record labels. Then, the following is a definition of tree as a record type:

$$
\text { tree } \mathrm{X} \approx \Pi(\text { root }: \mathrm{X} ; \text { sons }: \text { list }(\text { tree } \mathrm{X}))
$$

This definition is again recursive, and relies on the previous definition. Because list is covariant, it is straightforward to check that the definition of tree is valid if tree is made a covariant type constructor as well.

1.9.10 EXERCISE $[\star \star, \nrightarrow]$ : Consider a nonrecursive algebraic data type definition, where the variance of every type constructor that appears on the right-hand side is known. Can you systematically determine, for each of the parameters, the least restrictive variance that makes the definition valid? Generalize this procedure to the case of recursive and mutually recursive algebraic data type definitions.

A prologue is a set of algebraic data type definitions, where each data type is defined at most once and where each data constructor or record label appears at most once. A program is a pair of a prologue and an expression. The effect of a prologue is to enrich the programming language with new constants. That is, a variant type definition extends the operational semantics with several injections and a case construct, as in Example 1.2.7. A record type definition extends it with a record formation construct and several projections, as in Examples 1.2.3 and 1.2.5. In either case, the initial typing environment $\Gamma_{0}$ is extended with information about these new constants. Thus, algebraic data type definitions might be viewed as a simple configuration language that allows specifying in which instance of ML-the-calculus the expression that follows the prologue should be typechecked and interpreted. Let us now give a precise account of this phenomenon.

To begin, suppose the prologue contains the definition $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \sum_{i=1}^{k} \ell_{i}: \mathrm{T}_{i}$. Then, for each $i \in\{1, \ldots, k\}$, a constructor of arity 1 , named $\ell_{i}$, is introduced. Furthermore, a destructor of arity $k+1$, named case D $_{D}$, is introduced. When $k>0$, it is common to write case $\mathrm{t}\left[\ell_{i}: \mathrm{t}_{i}\right]_{i=1}^{k}$ for the application case $_{D} t t_{1} \ldots t_{n}$. The operational semantics is extended with the following reduction rules, for $i \in\{1, \ldots, k\}$ :

$$
\begin{equation*}
\operatorname{case}\left(\ell_{i} \mathrm{v}\right)\left[\ell_{j}: \mathrm{v}_{j}\right]_{j=1}^{k} \xrightarrow{\delta} \mathrm{v}_{i} \mathrm{v} \tag{R-ALG-CASE}
\end{equation*}
$$

For each $i \in\{1, \ldots, k\}$, the initial environment is extended with the binding $\ell_{i}: \forall \overline{\mathrm{X}} . \mathrm{T}_{i} \rightarrow \mathrm{D} \overrightarrow{\mathrm{X}}$. It is further extended with the binding case $\mathrm{D}_{\mathrm{D}}: \forall \overline{\mathrm{X}} \mathrm{Z} . \mathrm{D} \overrightarrow{\mathrm{X}} \rightarrow$ $\left(\mathrm{T}_{1} \rightarrow \mathrm{Z}\right) \rightarrow \ldots\left(\mathrm{T}_{k} \rightarrow \mathrm{Z}\right) \rightarrow \mathrm{Z}$.

Now, suppose the prologue contains the definition $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \prod_{i=1}^{k} \ell_{i}: \mathrm{T}_{i}$. Then, for each $i \in\{1, \ldots, k\}$, a destructor of arity 1 , named $\ell_{i}$, is introduced. Furthermore, a constructor of arity $k$, named make $\mathrm{e}_{\mathrm{D}}$, is introduced. It is common to write $\mathrm{t} . \ell$ for the application $\ell \mathrm{t}$ and, when $k>0$, to write $\left\{\ell_{i}=\mathrm{t}_{i}\right\}_{i=1}^{k}$ for the application make $\mathrm{t}_{\mathrm{D}} \ldots \mathrm{t}_{k}$. The operational semantics is extended with the following reduction rules, for $i \in\{1, \ldots, k\}$ :

$$
\begin{equation*}
\left(\left\{\ell_{j}=\mathrm{v}_{j}\right\}_{j=1}^{k}\right) \cdot \ell_{i} \xrightarrow{\delta} \mathrm{v}_{i} \tag{R-ALG-PRoJ}
\end{equation*}
$$

For each $i \in\{1, \ldots, k\}$, the initial environment is extended with the binding $\ell_{i}: \forall \overline{\mathrm{X}} . \mathrm{D} \overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}_{i}$. It is further extended with the binding make $\mathrm{D}_{\mathrm{D}}: \forall \overline{\mathrm{X}} . \mathrm{T}_{1} \rightarrow \ldots \rightarrow$ $\mathrm{T}_{k} \rightarrow \mathrm{D} \overrightarrow{\mathrm{X}}$.

1.9.11 EXAMPLE: The effect of defining list (Example 1.9.9) is to make Nil and Cons data constructors of arity 1 and to introduce a binary destructor case list . The definition also extends the initial environment as follows:

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-090.jpg?height=140&width=887&top_left_y=1880&top_left_x=712)

Thus, the value Cons $(\hat{0}, \mathrm{Nil}())$, an integer list of length 1 , has type list int. A function that computes the length of a list may now be written as follows:

$$
\text { letrec length }=\lambda l . \text { case } 1\left[\mathrm{Nil}: \lambda \_. \hat{0} \mid \text { Cons }: \lambda z . \hat{1} \hat{+} \text { length }\left(\pi_{2} z\right)\right]
$$

Recall that this notation is syntactic sugar for

$$
\text { letrec length }=\lambda \text { l.case }_{\text {list }} l\left(\lambda \_. \hat{0}\right)\left(\lambda z . \hat{1} \hat{+} \text { length }\left(\pi_{2} z\right)\right)
$$

The difference with the code in Example 1.9.7 appears minimal: the case construct is now annotated with the data type list. As a result, the type inference algorithm employs the type scheme assigned to case list , which is derived from the definition of list, instead of the type scheme assigned to the anonymous case construct, given in Exercise 1.9.4. This is good for a couple of reasons. First, the former is more informative than the latter, because it contains the type $\mathrm{T}_{i}$ associated with the data constructor $\ell_{i}$. Here, for instance, the generated constraint requires the type of $\mathrm{z}$ to be $\mathrm{X} \times$ list $\mathrm{X}$ for some $\mathrm{X}$, so a good error message would be given if a mistake was made in the second branch, such as omitting the use of $\pi_{2}$. Second, and more fundamentally, the code is now well-typed, even in the absence of recursive types. In Example 1.9.7, a cyclic equation was produced because case required the type of 1 to be a sum type and because a sum type carries the types of its left and right branches as subterms. Here, instead, case list requires 1 to have type list X for some X. This is an abstract type: it does not explicitly contain the types of the branches. As a result, the generated constraint no longer involves a cyclic equation. It is, in fact, satisfiable; the reader may check that length has type $\forall x$. list $X \rightarrow$ int, as expected.

Example 1.9.11 stresses the importance of using declared, abstract types, as opposed to anonymous, concrete sum or product types, in order to obviate the need for recursive types. The essence of the trick lies in the fact that the type schemes associated with operations on algebraic data types implicitly fold and unfold the data type's definition. More precisely, let us recall the type scheme assigned to the $i^{\text {th }}$ injection in the setting of ( $k$-ary) anonymous sums: it is $\forall \mathrm{X}_{1} \ldots \mathrm{X}_{k} \cdot \mathrm{X}_{i} \rightarrow \mathrm{X}_{1}+\ldots+\mathrm{X}_{k}$, or, more concisely, $\forall \mathrm{x}_{1} \ldots \mathrm{X}_{k} . \mathrm{X}_{i} \rightarrow \sum_{i=1}^{k} \mathrm{X}_{i}$. By instantiating each $\mathrm{X}_{i}$ with $\mathrm{T}_{i}$ and generalizing again, we find that a more specific type scheme is $\forall \overline{\mathrm{X}} . \mathrm{T}_{i} \rightarrow \sum_{i=1}^{k} \mathrm{~T}_{i}$. Perhaps this could have been the type scheme assigned to $\ell_{i}$ ? Instead, however, it is $\forall \overline{\mathrm{X}}$. $\mathrm{T}_{i} \rightarrow \mathrm{D} \overrightarrow{\mathrm{X}}$. We now realize that this type scheme not only reflects the operational behavior of the $i^{\text {th }}$ injection, but also folds the definition of the algebraic data type $\mathrm{D}$ by turning the anonymous sum $\sum_{i=1}^{k} \mathrm{~T}_{i}$-which forms the definition's right-hand side-into the parameterized abstract type $D \vec{X}$ - which is the definition's left-hand side. Conversely, the type scheme assigned to case $_{D}$ unfolds the definition. The
situation is identical in the case of record types: in either case, constructors fold, destructors unfold. In other words, occurrences of data constructors and record labels in the code may be viewed as explicit instructions for the typechecker to fold or unfold an algebraic data type definition. This mechanism is characteristic of isorecursive types.

1.9.12 EXERCISE $[\star, \nrightarrow]$ : For a fixed $k$, check that all of the machinery associated with $k$-ary anonymous products - that is, constructors, destructors, reduction rules, and extensions to the initial typing environment-may be viewed as the result of a single algebraic data type definition. Conduct a similar check in the case of $k$-ary anonymous sums.

1.9.13 EXERCISE $[\star \star \star, \nrightarrow]$ : Check that the above definitions meet the requirements of Definition 1.7.6.

1.9.14 EXERCISE $[\star \star \star, \nrightarrow]$ : For sake of simplicity, we have assumed that data constructors are always of arity one. It is indeed possible to allow data constructors of any arity and define variants as $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \sum_{i=1}^{k} \ell_{i}: \overrightarrow{\mathrm{T}}_{i}$. For instance, the definition of list could then be list $\mathrm{X} \approx \Sigma(\mathrm{Nil}$; Cons $: \mathrm{X} \times$ list $\mathrm{X})$ and for instance $\operatorname{Cons}(\hat{0}, \mathrm{Nil})$ would be a list value. Make the necessary changes in the definitions above and check that they still meet the requirements of Definition 1.7.6.

In this formal presentation of algebraic data types, we have assumed that all algebraic data type definitions are known before the program is typechecked. This simplifying assumption is forced on us by the fact that we interpret constraints in a fixed model, that is, we assume a fixed universe of types. In practice, programming languages have module systems, which allow distinct modules to have distinct, partial views of the universe of types. Then, it becomes possible for each module to come with its own data type definitions. Interestingly, it is even possible, in principle, to split the definition of a single data type over several modules, yielding extensible algebraic data types. For instance, module $A$ might declare the existence of a parameterized variant type $\mathrm{D} \overrightarrow{\mathrm{x}}$, without giving its components. Later on, module $B$ might define a component $\ell: \mathrm{T}$, where $f t v(\mathrm{~T}) \subseteq \overline{\mathrm{X}}$. Such a definition makes $\ell$ a unary constructor with type scheme $\forall \overline{\mathrm{X}} . \mathrm{T} \rightarrow \mathrm{D} \overrightarrow{\mathrm{X}}$, as before. It becomes impossible, however, to introduce a destructor $\mathrm{case}_{\mathrm{D}}$, because the definition of an extensible variant type can never be assumed to be complete-other, unknown modules might extend it further. To compensate for its absence, one may supplement every constructor $\ell$ with a destructor $\ell^{-1}$, whose semantics is given by $\ell^{-1}(\ell \mathrm{v}) \mathrm{v}_{1} \mathrm{v}_{2} \xrightarrow{\delta} \mathrm{v}_{1} \mathrm{v}$ and $\ell^{-1}\left(\ell^{\prime} \mathrm{v}\right) \mathrm{v}_{1} \mathrm{v}_{2} \xrightarrow{\delta} \mathrm{v}_{2}\left(\ell^{\prime} \mathrm{v}\right)$ when $\ell \neq \ell^{\prime}$, and whose type scheme is $\forall \overline{\mathrm{x}} \mathrm{Z} . \mathrm{D} \overrightarrow{\mathrm{X}} \rightarrow(\mathrm{T} \rightarrow \mathrm{Z}) \rightarrow(\mathrm{D} \overrightarrow{\mathrm{X}} \rightarrow \mathrm{Z}) \rightarrow \mathrm{Z}$. When
pattern matching is available, $\ell^{-1}$ may in fact be defined in the language. MLthe-programming-language does not offer extensible algebraic data types as a language feature, but does have one built-in extensible variant type, namely the type exn of exceptions. Thus, it is possible to define new constructors for the type exn within any module. The price of this extra flexibility is that no exhaustive case analysis on values of type exn is possible.

One significant drawback of algebraic data type definitions resides in the fact that a label $\ell$ cannot be shared by two distinct variant or record type definitions. Indeed, every algebraic data type definition extends the calculus with new constants. Strictly speaking, our presentation does not allow a single constant $\mathrm{c}$ to be associated with two distinct definitions. Even if we did allow such a collision, the initial environment would contain two bindings for c, one of which would then become inaccessible. This phenomenon arises in actual implementations of ML-the-programming-language, where a new algebraic data type definition may hide some of the data constructors or record labels introduced by a previous definition. An elegant solution to this lack of expressiveness is discussed in Section 1.11.

\section*{Pattern matching}

Our presentation of products, sums and algebraic data types has remained within the setting of ML-the-calculus: that is, data structures have been built out of constructors, while the case analysis and record access operations have been viewed as destructors. Some syntactic sugar has been used to recover standard notations. The language is now expressive enough to allow defining and manipulating complex data structures, such as lists and trees. Yet, experience shows that programming in such a language is still somewhat cumbersome. Indeed, case analysis and record access are low-level operations: the former allows inspecting a tag and branching, while the latter allows dereferencing a pointer. In practice, one often needs to carry out more complex tasks, such as determining whether a data structure has a certain shape or whether two data structures have comparable shapes. Currently, the only way to carry out these tasks is to program an explicit sequence of low-level operations. It would be much preferable to extend the language so that it becomes directly possible to describe shapes, called patterns, and so that checking whether a patterns matches a value becomes an elementary operation. ML-the-programming-language offers this feature, called pattern matching. Although pattern matching may be added to ML-the-calculus by introducing a family of destructors, we rather choose to extend the calculus with a new match construct, which subsumes the existing let construct. This approach appears somewhat simpler and more powerful. We now carry out this

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-094.jpg?height=383&width=1520&top_left_y=224&top_left_x=240)

Figure 1-13: Patterns and pattern matching

extension.

Let us first define the syntax of patterns (Figure 1-13) and describe (informally, for now) which values they match. To a pattern $\mathrm{p}$, we associate a set of defined program variables $d p i(\mathrm{p})$, whose definition appears in the text that follows. The pattern $\mathrm{p}$ is well-formed if and only if $d p i(\mathrm{p})$ is defined. To begin, the wildcard _ is a pattern, which matches every value and binds no variables. We let $d p i\left(\_\right)=\varnothing$. Although the wildcard may be viewed as an anonymous variable, and we have done so thus far, it is now simpler to view it as a distinct pattern. A program variable $z$ is also a pattern, which matches every value and binds $\mathbf{z}$ to the matched value. We let $d p i(\mathbf{z})=\{\mathbf{z}\}$. Next, if $\mathrm{c}$ is a constructor of arity $k$, then $\mathrm{c} \mathrm{p}_{1} \ldots \mathrm{p}_{k}$ is a pattern, which matches $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k}$ when $\mathrm{p}_{i}$ matches $\mathrm{v}_{i}$ for every $i \in\{1, \ldots, k\}$. We let $d p i\left(\mathrm{c}_{1} \ldots \mathrm{p}_{k}\right)=d p i\left(\mathrm{p}_{1}\right) \uplus \ldots \uplus d p i\left(\mathrm{p}_{k}\right)$. That is, the pattern $\mathrm{c} \mathrm{p}_{1} \ldots \mathrm{p}_{k}$ is well-formed when $\mathrm{p}_{1}, \ldots, \mathrm{p}_{k}$ define disjoint sets of variables. This condition rules out nonlinear patterns such as $(z, z)$. Defining the semantics of such a pattern would require a notion of equality at every type, which introduces various complications, so it is commonly considered ill-formed. The pattern $\mathrm{p}_{1} \wedge \mathrm{p}_{2}$ matches all values that both $\mathrm{p}_{1}$ and $\mathrm{p}_{2}$ match. It is commonly used with $\mathrm{p}_{2}$ a program variable: then, it allows examining the shape of a value and binding a name to it at the same time. Again, we define $d p i\left(\mathrm{p}_{1} \wedge \mathrm{p}_{2}\right)=d p i\left(\mathrm{p}_{1}\right) \uplus d p i\left(\mathrm{p}_{2}\right)$. The pattern $\mathrm{p}_{1} \vee \mathrm{p}_{2}$ matches all values that either $\mathrm{p}_{1}$ or $\mathrm{p}_{2}$ matches. We define $d p i\left(\mathrm{p}_{1} \vee \mathrm{p}_{2}\right)=d p i\left(\mathrm{p}_{1}\right)=d p i\left(\mathrm{p}_{2}\right)$. That is, the pattern $\mathrm{p}_{1} \vee \mathrm{p}_{2}$ is well-formed when $p_{1}$ and $p_{2}$ define the same variables. Thus, $\left(i n j_{1} z\right) \vee\left(i n j_{2} z\right)$ is a wellformed pattern, which binds $z$ to the component of a binary sum, without regard for its tag. However, $\left(i n j_{1} z_{1}\right) \vee\left(i n j_{2} z_{2}\right)$ is ill-formed, because one cannot statically predict whether it defines $z_{1}$ or $z_{2}$.

Let us now formally define whether a pattern $\mathrm{p}$ matches a value $\mathrm{v}$ and how the variables in $d p i(\mathrm{p})$ become bound to values in the process. This is done by introducing a generalized substitution, written $[\mathrm{p} \mapsto \mathrm{v}]$, which is either

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-095.jpg?height=296&width=1510&top_left_y=227&top_left_x=232)

undefined or a substitution of values for the program variables in $d p i(\mathrm{p})$. If the former, then $\mathrm{p}$ does not match $\mathrm{v}$. If the latter, then $\mathrm{p}$ matches $\mathrm{v}$ and, for every $\mathrm{z} \in d p i(\mathrm{p})$, the variable $\mathrm{z}$ becomes bound to the value $[\mathrm{p} \mapsto \mathrm{v}] \mathrm{z}$. Of course, when $\mathrm{p}$ is a variable $\mathrm{z}$, the generalized substitution $[\mathrm{z} \mapsto \mathrm{v}]$ is defined and coincides with the substitution $[\mathrm{z} \mapsto \mathrm{v}]$, which justifies our abuse of notation. To construct generalized substitutions, we use two simple combinators. First, when $\operatorname{dpi}\left(\mathrm{p}_{1}\right)$ and $\operatorname{dpi}\left(\mathrm{p}_{2}\right)$ are disjoint, $\left[\mathrm{p}_{1} \mapsto \mathrm{v}_{1}\right] \otimes\left[\mathrm{p}_{2} \mapsto \mathrm{v}_{2}\right]$ stands for the set-theoretic union of $\left[\mathrm{p}_{1} \mapsto \mathrm{v}_{1}\right]$ and $\left[\mathrm{p}_{2} \mapsto \mathrm{v}_{2}\right]$, if both are defined, and is undefined otherwise. We use this combinator to ensure that $\mathrm{p}_{1}$ matches $\mathrm{v}_{1}$ and $\mathrm{p}_{2}$ matches $\mathrm{v}_{2}$ and to combine the two corresponding sets of bindings. Second, when $o_{1}$ and $o_{2}$ are two possibly undefined mathematical objects that belong to the same space when defined, $o_{1} \oplus o_{2}$ stands for $o_{1}$, if it is defined, and for $o_{2}$ otherwise - that is, $\oplus$ is an angelic choice operator with a left bias. In particular, when $d p i\left(\mathrm{p}_{1}\right)$ and $d p i\left(\mathrm{p}_{2}\right)$ coincide, $\left[\mathrm{p}_{1} \mapsto \mathrm{v}_{1}\right] \oplus\left[\mathrm{p}_{2} \mapsto \mathrm{v}_{2}\right]$ stands for $\left[\mathrm{p}_{1} \mapsto \mathrm{v}_{1}\right]$, if it is defined, and for $\left[\mathrm{p}_{2} \mapsto \mathrm{v}_{2}\right]$ otherwise. We use this combinator to ensure that $\mathrm{p}_{1}$ matches $\mathrm{v}_{1}$ or $\mathrm{p}_{2}$ matches $\mathrm{v}_{2}$ and to retain the corresponding set of bindings. The full definition of generalized substitutions, which relies on these combinators, appears in Figure 1-13. It reflects the informal presentation of the previous paragraph.

Once patterns and pattern matching are defined, it is straightforward to extend the syntax and operational semantics of ML-the-calculus. We enrich the syntax of expressions with a new construct, match $\mathrm{t}$ with $\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$, where $k \geq 1$. It consists of a term $t$ and a nonempty, ordered list of clauses, each of which is composed of a pattern $\mathrm{p}_{i}$ and a term $\mathrm{t}_{i}$. The syntax of evaluation contexts is extended as well, so that the term $t$ that is being examined is first reduced to a value $\mathrm{v}$. The operational semantics is extended with a new rule, $\mathrm{R}-\mathrm{MATCH}$, which states that match $\mathrm{v}$ with $\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$ reduces to $\left[\mathrm{p}_{i} \mapsto \mathrm{v}\right] \mathrm{t}_{i}$, where $i$ is the least element of $\{1, \ldots, k\}$ such that $\mathrm{p}_{i}$ matches $\mathrm{v}_{i}$. Technically, $\bigoplus_{i=1}^{k}\left[\mathrm{p}_{i} \mapsto \mathrm{v}\right] \mathrm{t}_{i}$ stands for $\left[\mathrm{p}_{1} \mapsto \mathrm{v}\right] \mathrm{t}_{1} \oplus \ldots \oplus\left[\mathrm{p}_{k} \mapsto \mathrm{v}\right] \mathrm{t}_{k}$, so that the reduct is the first term that is defined in this sequence.

As far as semantics is concerned, the match construct may be viewed as a
generalization of the let construct. Indeed, let $z=t_{1}$ in $t_{2}$ may now be viewed as syntactic sugar for match $t_{1}$ with $z . t_{2}$, that is, a match construct with a single clause and a variable pattern. Then, R-LET becomes a special case of R-MATCH.

It is pleasant to introduce some more syntactic sugar. We write $\lambda\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$ for $\lambda$ z.match $\mathrm{z}$ with $\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$, where $\mathrm{z}$ is fresh for $\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$. Thus, it becomes possible to define functions by cases - a common idiom in ML-theprogramming-language.

1.9.15 EXAMPLE: Using pattern matching, a function that computes the length of a list (Example 1.9.11) may now be written as follows:

$$
\text { letrec length }=\lambda\left(\mathrm{Nil}_{\ldots} . \hat{0} \mid \operatorname{Cons}\left(\_, z\right) . \hat{1} \hat{+} \text { length } z\right)
$$

The second pattern matches a nonempty list and binds $\mathrm{z}$ to its tail at the same time, obviating the need for an explicit application of $\pi_{2}$.

1.9.16 Exercise $[\star \star$, Recommended, $\nrightarrow$ ]: Under the above definition of length, consider an application of length to the list Cons( $\hat{0}, \mathrm{Nil}())$. After eliminating the syntactic sugar, determine by which reduction sequence this expression reduces to a value.

Before we can proceed and extend the type system to deal with the new match construct, we must make two mild extensions to the syntax and meaning of constraints. First, if $\sigma$ is $\forall \overline{\mathrm{X}}[C]$.T, where $\overline{\mathrm{X}} \# f t v\left(\mathrm{~T}^{\prime}\right)$, then $\mathrm{T}^{\prime} \preceq \sigma$ stands for the constraint $\exists \overline{\mathrm{X}} .\left(C \wedge \mathrm{T}^{\prime} \leq \mathrm{T}\right)$. This relation is identical to the instance relation (Definition 1.3.3), except the direction of subtyping is reversed. We extend the syntax of constraints with instantiation constraints of the form $\mathrm{T} \preceq \mathrm{x}$ and define their meaning by adding a symmetric counterpart of CM-

INSTANCE. We remark that, when subtyping is interpreted as equality, the relations $\sigma \preceq \mathrm{T}$ and $\mathrm{T} \preceq \sigma$ coincide, so this extension is unnecessary in that particular case. Second, we extend the syntax of environments so that several successive bindings may share a set of quantifiers and a constraint. That is, we allow writing $\forall \overline{\mathrm{X}}[C] .\left(\mathrm{x}_{1}: \mathrm{T}_{1} ; \ldots ; \mathrm{x}_{k}: \mathrm{T}_{k}\right)$ for $\mathrm{x}_{1}: \forall \overline{\mathrm{x}}[C] . \mathrm{T}_{1} ; \ldots ; \mathrm{x}_{k}$ : $\forall \overline{\mathrm{X}}[C] . \mathrm{T}_{k}$. From a theoretical standpoint, this is little more than syntactic sugar; however, in practice, it is useful to implement this new idiom literally, since it avoids unnecessary copying of the constraint $C$.

Let us now extend the type system. For the sake of brevity, we extend the constraint generation rules only. Of course, it would also be possible to define corresponding extensions of the rule-based type systems shown earlier, namely $\mathrm{DM}, \operatorname{HM}(X)$, and $\operatorname{PCB}(X)$. We begin by defining a constraint $\llbracket \mathrm{T}: \mathrm{p} \rrbracket$ that represents a necessary and sufficient condition for values of type $\mathrm{T}$ to be acceptable inputs for the pattern $\mathrm{p}$. Its free type variables are a subset of

$$
\begin{aligned}
& \llbracket \mathrm{T}: \_\rrbracket=\text { true } \\
& \llbracket \mathrm{T}: \mathrm{z} \rrbracket=\mathrm{T} \preceq \mathrm{z} \\
& \llbracket \mathrm{T}: \mathrm{c} \mathrm{p}_{1} \cdots \mathrm{p}_{k} \rrbracket=\exists \overline{\mathrm{x}} \cdot\left(\overrightarrow{\mathrm{x}} \rightarrow \mathrm{T} \preceq \mathrm{c} \wedge \wedge_{i=1}^{k} \llbracket \mathrm{x}_{i}: \mathrm{p}_{i} \rrbracket\right) \\
& \llbracket \mathrm{T}: \mathrm{p}_{1} \wedge \mathrm{p}_{2} \rrbracket=\llbracket \mathrm{T}: \mathrm{p}_{1} \rrbracket \wedge \llbracket \mathrm{T}: \mathrm{p}_{2} \rrbracket \\
& \llbracket \mathrm{T}: \mathrm{p}_{1} \vee \mathrm{p}_{2} \rrbracket=\llbracket \mathrm{T}: \mathrm{p}_{1} \rrbracket \wedge \llbracket \mathrm{T}: \mathrm{p}_{2} \rrbracket \\
& \llbracket \text { matcht with }\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}: \mathrm{T} \rrbracket=\bigwedge_{i=1}^{k} \text { let } \forall \mathrm{x} \overline{\mathrm{x}}_{i}\left[\llbracket \mathrm{t}: \mathrm{x} \rrbracket \wedge \text { let } \overrightarrow{\mathrm{z}}_{i}: \overrightarrow{\mathrm{x}}_{i} \text { in } \llbracket \mathrm{x}: \mathrm{p}_{i} \rrbracket \rrbracket \cdot\left(\overrightarrow{\mathrm{z}}_{i}: \overrightarrow{\mathrm{x}}_{i}\right) \text { in } \llbracket \mathrm{t}_{i}: \mathrm{T} \rrbracket\right. \\
& \text { where } \overrightarrow{\mathrm{z}}_{i}=d p i\left(\mathrm{p}_{i}\right)
\end{aligned}
$$

Figure 1-15: Constraint generation for patterns and pattern matching

$f t v(T)$, while its free program identifiers are either constructors or program variables bound by $\mathrm{p}$. It is defined in the upper part of Figure 1-15. The first rule states that a wildcard matches values of arbitrary type. The second and third rules govern program variables and constructor applications in patterns. They are identical to the rules that govern these constructs in expressions (page 59), except that the direction of subtyping is reversed. In the absence of subtyping, they would be entirely identical. We write $\overrightarrow{\mathrm{X}}$ for $\mathrm{X}_{1} \ldots \mathrm{X}_{k}$ and $\overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}$ for $\mathrm{X}_{1} \rightarrow \ldots \rightarrow \mathrm{X}_{k} \rightarrow \mathrm{T}$. As usual, the type variables $\mathrm{X}_{1}, \ldots, \mathrm{X}_{k}$ must have kind $\star$ and must be distinct and fresh for the equation's left-hand side. The last two rules simply distribute the type $\mathrm{T}$ to both subpatterns. It is easy to check that $\llbracket \mathrm{T}: \mathrm{p} \rrbracket$ is contravariant in $\mathrm{T}$ :

1.9.17 Lemma: $\mathrm{T}^{\prime} \leq \mathrm{T} \wedge \llbracket \mathrm{T}: \mathrm{p} \rrbracket$ entails $\llbracket \mathrm{T}^{\prime}: \mathrm{p} \rrbracket$.

This property reflects the fact that $\mathrm{T}$ represents the type of an input for the pattern p. Compare it with Lemma 1.6.3.

1.9.18 Example: Consider the pattern Cons $\left({ }_{-}, \mathbf{z}\right)$, which appears in Example 1.9.15. We have

$$
\begin{aligned}
& \llbracket \mathrm{T}: \operatorname{Cons}(-\mathrm{z}) \rrbracket \\
\equiv & \exists \mathrm{Z}_{1} \cdot\left(\llbracket \mathrm{Z}_{1} \rightarrow \mathrm{T}: \text { Cons } \rrbracket \wedge \llbracket \mathrm{Z}_{1}:(, \mathrm{z}) \rrbracket\right) \\
\equiv & \exists \mathrm{Z}_{1} \cdot\left(\mathrm{Z}_{1} \rightarrow \mathrm{T} \preceq \text { Cons } \wedge \exists \mathrm{Z}_{2} \mathrm{Z}_{3} \cdot\left(\llbracket \mathrm{Z}_{2} \rightarrow \mathrm{Z}_{3} \rightarrow \mathrm{Z}_{1}:(\cdot, \cdot) \rrbracket \wedge \llbracket \mathrm{Z}_{2}: \_\rrbracket \wedge \llbracket \mathrm{Z}_{3}: \mathrm{z} \rrbracket\right)\right) \\
\equiv & \exists \mathrm{Z}_{1} \mathrm{Z}_{2} \mathrm{Z}_{3} \cdot\left(\mathrm{Z}_{1} \rightarrow \mathrm{T} \preceq \operatorname{Cons} \wedge \mathrm{Z}_{2} \rightarrow \mathrm{Z}_{3} \rightarrow \mathrm{Z}_{1} \preceq(\cdot, \cdot) \wedge \mathrm{Z}_{3} \preceq \mathrm{z}\right)
\end{aligned}
$$

where $\mathrm{Z}_{1}, \mathrm{Z}_{2}, \mathrm{Z}_{3}$ are fresh for $\mathrm{T}$. Let us now place this constraint within the scope of the initial environment, which assigns type schemes to the constructors Cons and $(\cdot, \cdot)$, and within the scope of a binding of $z$ to some type $\mathrm{T}^{\prime}$.

We find

$$
\begin{aligned}
& \text { let } \Gamma_{0} \text { in let } \mathrm{z}: \mathrm{T}^{\prime} \text { in } \llbracket \mathrm{T}: \text { Cons }(, \mathrm{z}) \rrbracket \\
\equiv & \exists \mathrm{Z}_{1} \mathrm{Z}_{2} \mathrm{Z}_{3} \cdot\left(\exists \mathrm{X} \cdot\left(\mathrm{Z}_{1} \rightarrow \mathrm{T} \leq \mathrm{X} \times \text { list } \mathrm{X} \rightarrow \text { list } \mathrm{X}\right) \wedge\right. \\
\equiv & \left.\exists \mathrm{Y}_{1} \mathrm{Y}_{2} \cdot\left(\mathrm{Z}_{2} \rightarrow \mathrm{Z}_{3} \rightarrow \mathrm{Z}_{1} \leq \mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2} \rightarrow \mathrm{Y}_{1} \times \mathrm{Y}_{2}\right) \wedge \mathrm{Z}_{3} \leq \mathrm{T}^{\prime}\right) \\
\equiv & \exists \mathrm{X} \cdot\left(\mathrm{T} \leq \text { list } \mathrm{X} \wedge \text { list } \mathrm{X} \leq \mathrm{T}^{\prime}\right)
\end{aligned}
$$

where the final simplification relies mainly on C-ARROw, on the corresponding rule for products, and on C-ExTrans, and is left as an exercise to the reader. Thus, the constraint states that the pattern matches values that have type list $\mathrm{X}$ (equivalently, values whose type $\mathrm{T}$ is a subtype of list $\mathrm{X}$ ), for some undetermined element type $\mathrm{X}$, and binds $\mathbf{z}$ to values of type list $\mathrm{X}$ (equivalently, values whose type $T^{\prime}$ is a supertype of list $X$ ).

The above example seems to indicate that the constraint generation rules for patterns make some sense. Still, the careful reader may be somewhat puzzled by the third rule, which, compared to its analogue for expressions, reverses the direction of subtyping, but does not reverse the direction of instantiation. Indeed, in order for this rule to make sense, and to be sound, we must formulate a requirement concerning the type schemes assigned to constructors.

1.9.19 Definition: A constructor $c$ is invertible if and only if, when $\vec{X}$ and $\vec{X}^{\prime}$ have length $a(\mathrm{c})$, the constraint let $\Gamma_{0}$ in $\left(\overrightarrow{\mathrm{X}}^{\prime} \rightarrow \mathrm{T} \preceq \mathrm{c} \wedge \mathrm{c} \preceq \overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}\right)$ entails $\overrightarrow{\mathrm{X}} \leq \overrightarrow{\mathrm{X}}^{\prime}$. In the following, we assume patterns contain invertible constructors only.

Intuitively, when $\mathrm{c}$ is invertible, it is possible to recover the type of every $\mathrm{v}_{i}$ from the type of $c \mathrm{v}_{1} \ldots \mathrm{v}_{k}$, a crucial property for pattern matching to be possible. Please note that, if $\Gamma_{0}(\mathrm{c})$ is monomorphic, then $\mathrm{c}$ is invertible. The following lemma identifies another important class of invertible constructors.

1.9.20 Lemma: The constructors of algebraic data types are invertible.

Proof: Let $\mathrm{c}$ be a constructor introduced by the definition of an algebraic data type D. Let $k=a(\mathrm{c})$. Then, the type scheme $\Gamma_{0}(\mathrm{c})$ is of the form $\forall \overline{\mathrm{Y}} . \overrightarrow{\mathrm{T}} \rightarrow \mathrm{D} \overrightarrow{\mathrm{Y}}$, where $\overrightarrow{\mathrm{Y}}$ are the parameters of the definition and $\overrightarrow{\mathrm{T}}$, a vector of length $k$, consists of some of the definition's components. (More precisely, $\overrightarrow{\mathrm{T}}$ contains just one component in the case of variant types and contains all components in the case of record types.) Let $\overrightarrow{\mathrm{X}}$ and $\overrightarrow{\mathrm{X}}^{\prime}$ have length $k$. Let $\forall \overrightarrow{\mathrm{Y}}_{1} \cdot \overrightarrow{\mathrm{T}}_{1} \rightarrow \mathrm{D} \overrightarrow{\mathrm{Y}}_{1}$ and $\forall \overline{\mathrm{Y}}_{2} \cdot \overrightarrow{\mathrm{T}}_{2} \rightarrow \mathrm{D} \overrightarrow{\mathrm{Y}}_{2}$ be two $\alpha$-equivalent forms of the type scheme $\Gamma_{0}(\mathrm{c})$, with $\overline{\mathrm{Y}}_{1} \# \overline{\mathrm{Y}}_{2}$ and $\overline{\mathrm{Y}}_{1} \overline{\mathrm{Y}}_{2} \# \operatorname{ftv}\left(\overline{\mathrm{X}}, \overline{\mathrm{X}}^{\prime}, \mathrm{T}\right)$. The constraint let $\Gamma_{0}$ in $\left(\overrightarrow{\mathrm{X}}^{\prime} \rightarrow \mathrm{T} \preceq \mathrm{c} \wedge \mathrm{c} \preceq\right.$ $\overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}$ ) is, by definition, equivalent to $\overrightarrow{\mathrm{X}}^{\prime} \rightarrow \mathrm{T} \prec \Gamma_{0}(\mathrm{c}) \wedge \Gamma_{0}(\mathrm{c}) \prec \overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}$, that is, $\exists \overline{\mathrm{Y}}_{1} \cdot\left(\overrightarrow{\mathrm{X}}^{\prime} \rightarrow \mathrm{T} \leq \overrightarrow{\mathrm{T}}_{1} \rightarrow \mathrm{D} \overrightarrow{\mathrm{Y}}_{1}\right) \wedge \exists \overline{\mathrm{Y}}_{2} \cdot\left(\overrightarrow{\mathrm{T}}_{2} \rightarrow \mathrm{D} \overrightarrow{\mathrm{Y}}_{2} \leq \overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}\right)$. By C-ExAND and CARRow, this may be written $\exists \bar{Y}_{1} \bar{Y}_{2} \cdot\left(D \vec{Y}_{2} \leq T \leq D \vec{Y}_{1} \wedge \vec{X} \leq \vec{T}_{2} \wedge \vec{T}_{1} \leq \vec{X}^{\prime}\right)$. Now,
by Definition 1.9.8, D $\overrightarrow{\mathrm{Y}}_{2} \leq \mathrm{D} \overrightarrow{\mathrm{Y}}_{1}$ entails $\overrightarrow{\mathrm{T}}_{2} \leq \overrightarrow{\mathrm{T}}_{1}$, so the previous constraint entails $\exists \bar{Y}_{1} \overline{\mathrm{Y}}_{2} \cdot\left(\overrightarrow{\mathrm{X}} \leq \overrightarrow{\mathrm{X}}^{\prime}\right)$, that is, $\overrightarrow{\mathrm{X}} \leq \overrightarrow{\mathrm{X}}^{\prime}$.

An important class of noninvertible constructors are those associated with existential type definitions (page 118), where not all quantifiers of the type scheme $\Gamma_{0}(c)$ are parameters of the type constructor D. For instance, under the definition $\mathrm{D} \approx \ell: \exists \mathrm{X} . \mathrm{X}$, the type scheme associated with $\ell$ is $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{D}$. Then, it is easy to check that $\ell$ is not invertible. This reflects the fact that it is not possible to recover the type of $\mathrm{v}$ from the type of $\ell \mathrm{v}$-which must be $D$ in any case-and explains why existential types require special treatment.

We are now ready to associate a constraint generation rule with the match construct. It is given in the lower part of Figure 1-15. In the rule's right-hand side, we write $\overrightarrow{\mathbf{z}}_{i}$ for the program variables bound by the pattern $\mathrm{p}_{i}$, and we write $\overrightarrow{\mathrm{X}}_{i}$ for a vector of type variables of the same length. The type variables $\mathrm{X} \overline{\mathrm{X}}_{i}$ must have kind $\star$, must be pairwise distinct and must not appear free in the rule's left-hand side. Let us now explain the rule. Its right-hand side is a conjunction, where each conjunct deals with one clause of the match construct, requiring $t_{i}$ to have type $T$ under certain assumptions about the program variables $\vec{z}_{i}$ bound by the pattern $\mathrm{p}_{i}$. There remains to explain how these assumptions are built. First, as in the case of a let construct, we summon a fresh type variable $\mathrm{X}$ and produce $\llbracket \mathrm{t}: \mathrm{x} \rrbracket$, the least specific constraint that guarantees $t$ has type $X$. Then, reflecting the operational semantics, which feeds (the value produced by) $t$ into the pattern $\mathrm{p}_{i}$, we feed the type $\mathrm{X}$ into $\mathrm{p}_{i}$ and produce let $\overrightarrow{\mathrm{z}}_{i}: \overrightarrow{\mathrm{X}}_{i}$ in $\llbracket \mathrm{X}: \mathrm{p}_{i} \rrbracket$, a constraint that guarantees that $\overrightarrow{\mathrm{X}}_{i}$ is a correct vector of type assumptions for the program variables $\vec{z}_{i}$ (see Example 1.9.18). This explains why we may place $\llbracket \mathrm{T}: \mathrm{t}_{i} \rrbracket$ within the scope of $\left(\vec{z}_{i}: \overrightarrow{\mathrm{x}}_{i}\right)$. There remains to point out that, as in the case of the let construct, every assignment of ground types to $\mathrm{X} \overline{\mathrm{X}}_{i}$ that satisfies the constraint $\llbracket \mathrm{t}: \mathrm{X} \rrbracket \wedge$ let $\overrightarrow{\mathrm{z}}_{i}: \overrightarrow{\mathrm{X}}_{i}$ in $\llbracket \mathrm{X}: \mathrm{p}_{i} \rrbracket$ is acceptable, so it is valid to universally quantify these type variables. This allows the program variables $\vec{z}_{i}$ to receive polymorphic type schemes when $t$ itself has polymorphic type.

1.9.21 Exercise [ $\star$, Recommended]: We have previously suggested viewing let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}$ as syntactic sugar for match $\mathrm{t}_{1}$ with $\mathrm{z} . \mathrm{t}_{2}$, and shown that the operational semantics validates this view. Check that it is also valid from a typing perspective.

The match constraint generation rule, if implemented literally, takes $k$ copies of the constraint $\llbracket \mathrm{t}: \mathrm{x} \rrbracket$. When $k$ is greater than 1 , this compromises the linear time and space complexity of constraint generation. To remedy this problem, one may modify the rule as follows: replace every copy of $\llbracket t: x \rrbracket$ with $z \preceq x$ and place the constraint within the context let $z: \forall x[\llbracket t: x \rrbracket] . x$ in [] , where $z$ is
a fresh program variable. It is not difficult to check that the logical meaning of the constraint is not affected and that a linear behavior is recovered. In practice, solving the new constraint requires taking instances of the type scheme $\forall x[\llbracket t: x \rrbracket] . x$, which essentially requires copying $\llbracket t: x \rrbracket$ again-however, an efficient solver may now simplify this subconstraint before duplicating it.

The following lemma is a key to establishing subject reduction for RMATCH. It relies on the requirement that constructors be invertible.

1.9.22 Lemma: Assume $[\mathrm{p} \mapsto \mathrm{v}]$ is defined and maps $\overrightarrow{\mathrm{z}}$ to $\overrightarrow{\mathrm{w}}$, where $\overline{\mathbf{z}}=d p i(\mathrm{p})$. Let $\vec{z}: \vec{T}$ be an arbitrary monomorphic environment of domain $\bar{z}$. Then, let $\Gamma_{0}$ in $(\llbracket \mathrm{v}: \mathrm{T} \rrbracket \wedge$ let $\overrightarrow{\mathrm{z}}: \overrightarrow{\mathrm{T}}$ in $\llbracket \mathrm{T}: \mathrm{p} \rrbracket)$ entails let $\Gamma_{0}$ in $\llbracket \overrightarrow{\mathrm{w}}: \overrightarrow{\mathrm{T}} \rrbracket$.

We now prove that our extension of ML-the-calculus with pattern matching enjoys subject reduction. We only state that R-MATCH preserves types, and leave the new subcase of R-CONTEXT, where the evaluation context involves a match construct, to the reader. For this subcase to succeed, the value restriction (Definition 1.7.7) must be extended to require that either all constants have pure semantics or all match constructs are in fact of the form match v with $\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$.

\subsection*{1.9.23 ThEOREM [SUBJECT REDUCTION]: (R-MATCH) $\subseteq(\sqsubseteq)$}

1.9.24 ExERcise $[\star \star \star, \nrightarrow]$ : For the sake of simplicity, we have omitted the production ref $p$ from the syntax of patterns. The pattern ref $p$ matches every memory location whose content (with respect to the current store) is matched by p. Determine how the previous definitions and proofs must be extended in order to accommodate this new production.

The progress property does not hold in general: for instance, match Nil with (Cons z.z) is well-typed (with type $\forall$ X.X) but is stuck. In actual implementations of ML-the-programming-language, such errors are dynamically detected. This may be considered a weakness of ML-the-typesystem. Fortunately, however, it is often possible to statically prove that a particular match construct is exhaustive and cannot go wrong. Indeed, if match $\mathrm{v}$ with $\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$ is well-typed, then for every $i \in\{1, \ldots, k\}$, the constraint let $\Gamma_{0}$ in $\left(\llbracket \mathrm{v}: \mathrm{X} \rrbracket \wedge \exists \overline{\mathrm{X}}\right.$. let $\overrightarrow{\mathrm{z}}_{i}: \overrightarrow{\mathrm{X}}$ in $\left.\llbracket \mathrm{X}: \mathrm{p}_{i} \rrbracket\right)$, where $\overline{\mathrm{z}}_{i}$ are the program variables bound by $\mathrm{p}_{i}$, must be satisfiable; that is, $\mathrm{v}$ must have some type that is an acceptable input for $\mathrm{p}_{i}$. This fact yields information about $\mathrm{v}$, from which it may be possible to derive that $\mathrm{v}$ must match one of the patterns $\mathrm{p}_{i}$.

1.9.25 ExAmple: Let $k=2, \mathrm{p}_{1}=\mathrm{Nil}$, and $\mathrm{p}_{2}=$ Cons $\left(\mathbf{z}_{1}, \mathbf{z}_{2}\right)$. Then, the constraints let $\Gamma_{0}$ in $\exists \overline{\mathrm{X}}$.let $\overrightarrow{\mathrm{z}}_{i}: \overrightarrow{\mathrm{X}}$ in $\llbracket \mathrm{X}: \mathrm{p}_{i} \rrbracket$, for $i \in\{1,2\}$, are both equivalent (after simplification, when $i=2$ ) to $\exists \mathrm{Z}$. $\mathrm{X} \leq$ list $\mathrm{Z}$. Because the type constructor list is isolated, every closed value $\mathrm{v}$ whose type $\mathrm{X}$ satisfies this constraint
must be an application of $\mathrm{Nil}$ or Cons. If the latter, because Cons has type $\forall \mathrm{X} . \mathrm{X} \times$ list $\mathrm{X} \rightarrow$ list $\mathrm{X}$, and because the type constructor $\times$ is isolated, the argument to Cons must be a pair. We conclude that $v$ must match either $\mathrm{p}_{1}$ or $\mathrm{p}_{2}$, which guarantees that this match construct is exhaustive and its evaluation cannot go wrong.

It is beyond the scope of this chapter to give more details about the check for exhaustiveness. The reader is referred to (Sekar, Ramesh, and Ramakrishnan, 1995; Le Fessant and Maranget, 2001).

\section*{Type annotations}

So far, we have been interested in a very pure, and extreme, form of type inference. Indeed, in ML-the-calculus, expressions contain no explicit type information whatsoever: it is entirely inferred. In practice, however, it is often useful to insert type annotations within expressions, because they provide a form of machine-checked documentation. Type annotations are also helpful when attempting to trace the cause of a type error: by supplying the typechecker with (supposedly) correct type information, one runs a better chance of finding a type inconsistency near an actual programming mistake.

When type annotations are allowed to contain type variables, one must be quite careful about where (at which program point) and how (existentially or universally) these variables are bound. Indeed, the meaning of type annotations cannot be made precise without settling these issues. In what follows, we first explain how to introduce type annotations whose type variables are bound locally and existentially. We show that extending ML-the-calculus with such limited type annotations is again a simple matter of introducing new constants. Then, we turn to a more general case, where type variables may be explicitly existentially introduced at any program point. We defer the discussion of universally bound type variables to Section 1.10.

Let a local existential type annotation $\exists \overline{\mathrm{X}}$. $\mathrm{T}$ be a pair of a set of type variables $\overline{\mathrm{X}}$ and a type $\mathrm{T}$, where $\mathrm{T}$ has kind $\star, \overline{\mathrm{X}}$ is considered bound within $\mathrm{T}$, and $\overline{\mathrm{X}}$ contains $f t v(\mathrm{~T})$. For every such annotation, we introduce a new unary destructor $(\cdot: \exists \overline{\mathrm{X}} . \mathrm{T})$. Such a definition is valid only because a type annotation must be closed, that is, does not have any free type variables. We write $(t: \exists \bar{X} . T)$ for the application $((\cdot: \exists \bar{X} . T)) t$. Since a type annotation does not affect the meaning of a program, the new destructor has identity semantics:

$$
(\mathrm{v}: \exists \overline{\mathrm{X}} . \mathrm{T}) \xrightarrow{\delta} \mathrm{v}
$$

(R-AnNotation)

Its type scheme, however, is not that of the identity, namely $\forall X . X \rightarrow X$ : instead, it is less general, so that annotating an expression restricts its type. Indeed,
we extend the initial environment $\Gamma_{0}$ with the binding

$$
(\cdot: \exists \overline{\mathrm{X}} . \mathrm{T}): \forall \overline{\mathrm{X}} . \mathrm{T} \rightarrow \mathrm{T}
$$

1.9.26 EXERCISE [ $\star$ ]: Check that $\forall \overline{\mathrm{X}} . \mathrm{T} \rightarrow \mathrm{T}$ is an instance of $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$ in Damas and Milner's sense, that is, the former is obtained from the latter via the rule DM-INST' given in Exercise 1.2.23. Does this allow arguing that the type scheme assigned to $(\cdot: \exists \overline{\mathrm{X}} . \mathrm{T})$ is sound? Check that the above definitions meet the requirements of Definition 1.7.6.

Although inserting a type annotation does not change the semantics of the program, it does affect constraint generation, hence type inference. We let the reader check that, assuming $\overline{\mathrm{X}} \# f t v\left(\mathrm{t}, \mathrm{T}^{\prime}\right)$, the following derived constraint generation rule holds:

$$
\text { let } \Gamma_{0} \text { in } \llbracket(\mathrm{t}: \exists \overline{\mathrm{X}} . \mathrm{T}): \mathrm{T}^{\prime} \rrbracket \equiv \text { let } \Gamma_{0} \text { in } \exists \overline{\mathrm{X}} \cdot\left(\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{T}^{\prime}\right)
$$

So far, expressions cannot have free type variables, so the hypothesis $\overline{\mathrm{x}}$ \# $f t v(\mathrm{t})$ may seem superfluous. However, we shall soon allow expressions to contain type annotations with free type variables, so we prefer to make this condition explicit now. According to this rule, the effect of the type annotation is to force the expression $t$ to have type $\mathrm{T}$, for some choice of the type variables $\overline{\mathrm{X}}$. As usual in type systems with subtyping, the expression's final type $\mathrm{T}^{\prime}$ may then be an arbitrary supertype of this particular instance of $\mathrm{T}$. When subtyping is interpreted as equality, $\mathrm{T}^{\prime}$ and $\mathrm{T}$ are equated by the constraint, so this constraint generation rule may be read: a valid type for ( $\mathrm{t}: \exists \overline{\mathrm{X}} \mathrm{T}$ ) must be of the form $\mathrm{T}$, for some choice of the type variables $\overline{\mathrm{x}}$.

1.9.27 Example: In DM extended with integers, the expression ( $\lambda z . z:$ int $\rightarrow$ int) has most general type int $\rightarrow$ int, even though the underlying identity function has most general type $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$, so the annotation restricts its type. The expression $(\lambda z . z \hat{+} \hat{1}: \exists X . X \rightarrow X)$ has type int $\rightarrow$ int, which is also the most general type of the underlying function, so the annotation acts merely as documentation in this case. Note that the type variable $\mathrm{X}$ is instantiated to int by the constraint solver. The expression $(\lambda z .(z \hat{1}): \exists X . X \rightarrow$ int) has type (int $\rightarrow$ int) $\rightarrow$ int because the underlying function has type (int $\rightarrow \mathrm{Y}) \rightarrow \mathrm{Y}$, which successfully unifies with $\mathrm{X} \rightarrow$ int by instantiating $\mathrm{X}$ to int $\rightarrow$ int and $\mathrm{Y}$ to int. Last, the expression ( $\lambda \mathrm{z} \cdot(\mathrm{z} \hat{1}): \exists \mathrm{X}$.int $\rightarrow \mathrm{X}$ ) is ill-typedeven though the underlying expression is well-typed-because the equation (int $\rightarrow \mathrm{Y}) \rightarrow \mathrm{Y}=$ int $\rightarrow \mathrm{X}$ is unsatisfiable.

1.9.28 ExAmple: In DM extended with pairs, the expression $\lambda z_{1} \cdot \lambda z_{2} \cdot\left(\left(z_{1}:\right.\right.$ $\left.\exists X . X),\left(z_{2}: \exists X . X\right)\right)$ has most general type $\forall X Y . X \rightarrow Y \rightarrow X \times Y$. In other words, the two occurrences of $X$ do not represent the same type. Indeed, one could just as well have written $\lambda z_{1} \cdot \lambda z_{2} \cdot\left(\left(z_{1}: \exists X . X\right),\left(z_{2}: \exists Y . Y\right)\right)$. If one wishes $z_{1}$ and $z_{2}$ to receive the same type, one must lift the type annotations and merge them above the pair constructor, as follows: $\lambda z_{1} \cdot \lambda z_{2} \cdot\left(\left(z_{1}, z_{2}\right): \exists X . X \times X\right)$. In the process, the type constructor $x$ has appeared in the annotation, causing its size to increase.

The above example reveals a limitation of this style of type annotations: by requiring every type annotation to be closed, we lose the ability for two separate annotations to share a type variable. Yet, such a feature is sometimes desirable. If the two annotations where sharing is desired are distant in the code, it may be awkward to lift and merge them into a single annotation; so, more expressive power is sometimes truly needed.

Thus, we are lead to consider more general type annotations, of the form $(\mathrm{t}: \mathrm{T})$, where $\mathrm{T}$ has kind $\star$, and where the type variables that appear within $\mathrm{T}$ are considered free, so that distinct type annotations may refer to shared type variables. For this idea to make sense, however, it is still necessary to specify where these type variables are bound. We do so using expressions of the form $\exists \overline{\mathrm{X}}$.t. Such an expression binds the type variables $\overline{\mathrm{X}}$ within the expression $t$, so that all free occurrences of $X$ (where $X \in \bar{X}$ ) in type annotations inside $t$ stand for the same type. Thus, we break the simple type annotation construct $(\cdot: \exists \overline{\mathrm{X}}$.T) into two more elementary constituents, namely existential type variable introduction $\exists \overline{\mathrm{X}} \cdot$ and type constraint $(\cdot: \mathrm{T})$. Note that both are new forms of expressions; neither can be encoded by adding new constants to the calculus, because it is not possible to assign closed type schemes to them.

Technically, allowing expressions to contain type variables requires some care. Several constraint generation rules employ auxiliary type variables, which become bound in the generated constraint. These type variables may be chosen in an arbitrary way, provided they do not appear free in the rule's left-hand side - a side-condition intended to avoid inadvertent capture. So far, this side-condition could be read: the auxiliary type variables used to form the constraint $\llbracket t: T \rrbracket$ must not appear free within $\mathrm{T}$. Now, since type annotations may contain free type variables, the side-condition becomes: the auxiliary type variables used to form $\llbracket \mathrm{t}: \mathrm{T} \rrbracket$ must not appear free within $\mathrm{t}$ or $\mathrm{T}$.

With this extended side-condition in mind, our original constraint generation rules remain unchanged. We add two new rules to describe how the new expression forms affect constraint generation:

$$
\begin{aligned}
\llbracket \exists \overline{\mathrm{X}} . \mathrm{t}: \mathrm{T} \rrbracket & =\exists \overline{\mathrm{X}} \cdot \llbracket \mathrm{t}: \mathrm{T} \rrbracket & \text { provided } \overline{\mathrm{X}} \# \mathrm{ftv}(\mathrm{T}) \\
\llbracket(\mathrm{t}: \mathrm{T}): \mathrm{T}^{\prime} \rrbracket & =\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{T}^{\prime} &
\end{aligned}
$$

The effect of these rules is simple. The construct $\exists \bar{x}$.t is an indication to the constraint generator that the type variables $\overline{\mathrm{X}}$, which may occur free within type annotations inside $t$, should be existentially bound at this point. The side-condition $\overline{\mathrm{X}}$ \# $f t v(\mathrm{~T})$ ensures that quantifying over $\overline{\mathrm{X}}$ in the generated constraint does not capture type variables in the expected type T. It can always be satisfied by $\alpha$-conversion of the expression $\exists \overline{\mathrm{X}}$.t. The construct ( $\mathrm{t}: \mathrm{T}$ ) is an indication to the constraint generator that the expression $t$ should have type $\mathrm{T}$, and it is treated as such by generating the subconstraint $\llbracket t: T \rrbracket$. The expression's type may be an arbitrary supertype of $\mathrm{T}$, hence the auxiliary constraint $\mathrm{T} \leq \mathrm{T}^{\prime}$.

1.9.29 EXAMPlE: In DM extended with pairs, the expression $\lambda z_{1} \cdot \lambda z_{2} \cdot \exists x .\left(\left(z_{1}\right.\right.$ : $\left.\mathrm{X}),\left(\mathrm{z}_{2}: \mathrm{X}\right)\right)$ has most general type $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X} \rightarrow \mathrm{X} \times \mathrm{X}$. Indeed, the constraint generated for this expression contains the pattern $\exists x .\left(\llbracket z_{1}: x \rrbracket \wedge \llbracket z_{2}: x \rrbracket \wedge \ldots\right)$, which causes $z_{1}$ and $z_{2}$ to receive the same type. Note that this style is more flexible than that employed in Example 1.9.28, where we were forced to use a single, monolithic type annotation to express this sharing constraint.

1.9.30 REMARK: In practice, a type variable is usually represented as a memory cell in the typechecker's heap. So, one cannot say that the source code contains type variables; rather, it contains names that are meant to stand for type variables. Let us write $X$ for such a name, and $T$ for a type made of type constructors and names, rather than of type constructors and type variables. Then, our new expression forms are really $\exists \bar{X}$.t and ( $\mathrm{t}: T$ ). When the constraint generator enters the scope of an introduction form $\exists \bar{X}$.t, it allocates a vector of fresh type variables $\overline{\mathrm{X}}$, and augments an internal environment with the bindings $\bar{X} \mapsto \overline{\mathrm{X}}$. Because the type variables are fresh, the side-condition of the first constraint generation rule above is automatically satisfied. When the constraint generator finds a type annotation ( $t: T$ ), it looks up the internal environment to translate the type annotation $T$ into an internal type $\mathrm{T}$-which fails if $T$ contains a name that is not in scope-and applies the second constraint generation rule above.

1.9.31 ExERcise $[\star \star, \nrightarrow]$ : Let $\overline{\mathrm{X}} \supseteq f t v(\mathrm{~T})$ and $\overline{\mathrm{X}} \# f t v(\mathrm{t})$. Check that the constraints $\llbracket(\mathrm{t}: \exists \overline{\mathrm{X}} . \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ and $\llbracket \exists \overline{\mathrm{X}} .(\mathrm{t}: \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ are equivalent. In other words, the local type annotations introduced earlier may be expressed in terms of the more complex constructs described above.

1.9.32 EXERCISE $[\star \star, \nrightarrow]$ : One way of giving identity semantics to our new type annotation constructs is to erase them altogether prior to execution. Give an inductive definition of $\lfloor t\rfloor$, the expression obtained by removing all type annotation constructs from the expression $t$. Check that $\llbracket t: T \rrbracket$ entails $\llbracket\lfloor t\rfloor$ : $\mathrm{T} \rrbracket$ and explain why this is sufficient to ensure type soundness.

It is interesting to study how explicit introduction of existentially quantified type variables interacts with let-polymorphism. The source of their interaction lies in the difference between the constraints let $\mathrm{z}: \forall \overline{\mathrm{x}}\left[\exists \mathrm{X} . C_{1}\right] . \mathrm{T}$ in $C_{2}$ and $\exists$ x.let $\mathrm{z}: \forall \overline{\mathrm{x}}\left[C_{1}\right] . \mathrm{T}$ in $C_{2}$, which was explained in Example 1.3.28. In the former constraint, every free occurrence of $\mathrm{z}$ inside $C_{2}$ causes a copy of $\exists \mathrm{x} . C_{1}$ to be taken, thus creating its own fresh copy of X. In the latter constraint, on the other hand, every free occurrence of $\mathrm{z}$ inside $C_{2}$ produces a copy of $C_{1}$. All such copies share references to $\mathrm{X}$, because its quantifier was not duplicated. In the former case, one may say that the type scheme assigned to $z$ is polymorphic with respect to $\mathrm{X}$, while in the latter case it is monomorphic. As a result, the placement of type variable introduction expressions with respect to let bindings in the source code is meaningful: introducing a type variable outside of a let construct prevents it from being generalized.

1.9.33 ExAmple: In DM extended with integers and Booleans, the program let $f=$ $\exists X . \lambda z .(z: X)$ in (f $0, f$ true $)$ is well-typed. Indeed, the type scheme assigned to $f$ is $\forall X . X \rightarrow X$. However, the program $\exists X$.let $f=\lambda z .(z: X)$ in ( $f 0, f$ true) is ill-typed. Indeed, the type scheme assigned to $f$ is $X \rightarrow X$; then, no value of $X$ satisfies the constraints associated with the applications $f 0$ and $f$ true. The latter behavior is observed in Objective Caml, where type variables are implicitly introduced at the outermost level of expressions:

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-105.jpg?height=89&width=995&top_left_y=1139&top_left_x=620)

More details about the treatment of type annotations in Standard ML, Objective Caml, and Haskell are given on page 113.

1.9.34 EXERcisE $[\star, \nrightarrow]$ : Determine which constraints are generated for the two programs in Example 1.9.33. Check that the former is indeed well-typed, while the latter is ill-typed.

\section*{Recursive types}

We have shown that specializing $\operatorname{HM}(X)$ with an equality-only syntactic model yields $\operatorname{HM}(=)$, a constraint-based formulation of Damas and Milner's type system. Similarly, it is possible to specialize $\operatorname{HM}(X)$ with an equalityonly free regular tree model, yielding a constraint-based type system that may be viewed as an extension of Damas and Milner's type discipline with recursive types. This flavor of recursive types is sometimes known as equirecursive, since cyclic equations, such as $\mathrm{X}=\mathrm{X} \rightarrow \mathrm{X}$, are then satisfiable. Our theorems about type inference and type soundness, which are independent of the model, remain valid. The constraint solver described in Section 1.8 may be used in
the setting of an equality-only free regular tree model: the only difference with the syntactic case is that the occurs check is no longer performed.

Please note that, although ground types are regular, types remain finite objects: their syntax is unchanged. The $\mu$ notation commonly employed to describe recursive types may be emulated using type equations: for instance, the notation $\mu \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$ corresponds, in our constraint-based approach, to the type scheme $\forall x[X=X \rightarrow X]$. $\mathrm{X}$.

Although recursive types come for free, as explained above, they have not been adopted in mainstream programming languages based on ML-the-typesystem. The reason is pragmatic: experience shows that many nonsensical expressions are well-typed in the presence of recursive types, whereas they are not in their absence. Thus, the gain in expressiveness is offset by the fact that many programming mistakes are detected later than otherwise possible. Consider, for instance, the following OCaml session:

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-106.jpg?height=202&width=956&top_left_y=862&top_left_x=602)

This nonsensical variant of map is essentially useless, yet well-typed. Its principal type scheme, in our notation, is $\forall \mathrm{XYZ}[\mathrm{Y}=$ list $\mathrm{Y} \wedge \mathrm{Z}=$ list $\mathrm{Z}] . \mathrm{X} \rightarrow \mathrm{Y} \rightarrow \mathrm{Z}$. In the absence of recursive types, it is ill-typed, since the constraint $Y=$ list $\mathrm{Y} \wedge \mathrm{Z}=$ list $\mathrm{Z}$ is then false.

The need for equirecursive types is usually suppressed by the presence of algebraic data types, which offer isorecursive types, in the language. Yet, they are still necessary in some situations, such as in Objective Caml's objectoriented extension (Rémy and Vouillon, 1998), where recursive object types are commonly inferred. In order to allow recursive object types while still rejecting the above variant of map, Objective Caml's constraint solver implements a selective occurs check, which forbids cycles unless they involve the type constructor $\langle\cdot\rangle$ associated with objects. The corresponding model is a tree model where every infinite path down a tree must encounter the type constructor $\langle\cdot\rangle$ infinitely often.

\subsection*{1.10 Universal quantification in constraints}

The constraint logic studied so far allows a set of variables $\overline{\mathrm{X}}$ to be existentially quantified within a formula $C$. The resulting formula $\exists \overline{\mathrm{x}}$. $C$ receives its standard meaning: it requires $C$ to hold for some $\overline{\mathrm{X}}$. However, we currently have no way of requiring a formula $C$ to hold for all $\overline{\mathrm{X}}$. Is it possible to extend our
logic with universal quantification? If so, what are the new possibilities offered by this extension, in terms of type inference? The present section proposes some answers to these questions.

It is worth noting that, although the standard notation for type schemes involves the symbol $\forall$, type scheme introduction and instantiation constraints do not allow an encoding of universal quantification. Indeed, a universal quantifier in a type scheme is very much like an existential quantifier in a constraint: this is suggested, for instance, by Definition 1.3.3 and by C-LETEx.

\section*{Constraints}

We extend the syntax of constraints as follows:

$$
C::=\ldots \mid \forall \overline{\mathrm{x}} . C
$$

Universally quantified variables are often referred to as rigid, while existentially quantified variables are known as flexible. The logical interpretation of constraints (Figure 1-5) is extended as follows:

$$
\begin{gather*}
\forall \vec{t} \quad \phi[\overrightarrow{\mathrm{x}} \mapsto \vec{t}] \vdash \operatorname{def} \Gamma \text { in } C \\
\overline{\mathrm{x}} \# f t v(\Gamma)  \tag{CM-ForALL}\\
\hline \vdash \operatorname{def} \Gamma \text { in } \forall \overline{\mathrm{x}} . C
\end{gather*}
$$

We let the reader check that none of the results established in Section 1.3 are affected by this addition. Furthermore, the extended constraint language enjoys the following properties.

1.10.1 Lemma: $\forall \overline{\mathrm{x}} . C \Vdash C$. Conversely, $\overline{\mathrm{x}} \# \operatorname{ftv}(C)$ implies $C \Vdash \forall \overline{\mathrm{x}} . C$.

1.10.2 Lemma: $\overline{\mathrm{X}} \# \operatorname{ftv}\left(C_{2}\right)$ implies $\forall \overline{\mathrm{x}} .\left(C_{1} \wedge C_{2}\right) \equiv\left(\forall \overline{\mathrm{x}} . C_{1}\right) \wedge C_{2}$.

1.10.3 Lemma: $\forall \overline{\mathrm{X}} . \forall \overline{\mathrm{Y}} . C \equiv \forall \overline{\mathrm{X}} \overline{\mathrm{Y}} . C$.

1.10.4 Lemma: Let $\overline{\mathrm{x}} \# \overline{\mathrm{Y}}$. Then, $\exists \overline{\mathrm{x}} . \forall \overline{\mathrm{Y}} . C$ entails $\forall \overline{\mathrm{Y}} . \exists \overline{\mathrm{X}} . C$. Conversely, if $\exists \overline{\mathrm{Y}} . C$ determines $\overline{\mathrm{X}}$, then $\forall \overline{\mathrm{Y}} . \exists \overline{\mathrm{X}} . C$ entails $\exists \overline{\mathrm{X}} . \forall \overline{\mathrm{Y}} . C$.

\section*{Constraint solving}

We briefly explain how to extend the constraint solver described in Section 1.8 with support for universal quantification. (Thus, we again assume an equalityonly free tree model.) Constraint solving in the presence of equations and of existential and universal quantifiers is known as unification under a mixed prefix. It is a particular case of the decision problem for the first-order theory of equality on trees; see e.g. (Comon and Lescanne, 1989). Extending our solver is straightforward: in fact, the treatment of universal quantifiers turns

$$
\begin{aligned}
& S ; U ; \forall \overline{\mathrm{x}} . C \quad \rightarrow \quad S[\forall \overline{\mathrm{x}} . \square] ; U ; C \\
& \text { if } \overline{\mathrm{x}} \# f t v(U) \\
& S[\forall \overline{\mathrm{X}} . \exists \overline{\mathrm{Y}} \overline{\mathrm{Z}} .[]] ; U ; \text { true } \quad \rightarrow \quad S[\exists \overline{\mathrm{Y}} . \forall \overline{\mathrm{X}} . \exists \overline{\mathrm{Z}} .[]] ; U ; \text { true } \\
& \text { if } \overline{\mathrm{X}} \# \overline{\mathrm{Y}} \wedge \exists \overline{\mathrm{X}} \overline{\mathrm{Z}} \cdot U \text { determines } \overline{\mathrm{Y}} \\
& S[\forall \overline{\mathrm{x}} \mathrm{X} . \exists \overline{\mathrm{Y}} .[]] ; U ; \text { true } \rightarrow \text { false } \\
& \text { if } \mathrm{X} \notin \overline{\mathrm{Y}} \wedge \mathrm{X} \prec_{U}^{\star} \mathrm{Z} \wedge \mathrm{Z} \notin \mathrm{X} \overline{\mathrm{Y}} \\
& S[\forall \overline{\mathrm{X}} \mathrm{X} . \exists \overline{\mathrm{Y}} . \square] ; \mathrm{X}=\mathrm{T}=\epsilon \wedge U ; \text { true } \rightarrow \text { false } \\
& \text { if } \mathrm{X} \notin \overline{\mathrm{Y}} \wedge \mathrm{T} \notin \mathcal{V} \\
& S[\forall \overline{\mathrm{X}} . \exists \overline{\mathrm{Y}} . \square] ; U_{1} \wedge U_{2} ; \text { true } \rightarrow S ; U_{1} ; \text { true } \\
& \text { if } \overline{\mathrm{X}} \overline{\mathrm{Y}} \# \operatorname{ftv}\left(U_{1}\right) \wedge \exists \overline{\mathrm{Y}} \cdot U_{2} \equiv \text { true }
\end{aligned}
$$

\section*{Figure 1-16: Solving universal constraints}

out to be surprisingly analogous to that of let constraints. To begin, we extend the syntax of stacks with so-called universal frames:

$$
S::=\ldots \mid S[\forall \overline{\mathrm{x}} . \square]
$$

Because existential quantifiers cannot, in general, be hoisted out of universal quantifiers, rules S-Ex-1 to S-Ex-4 now allow floating them up to the nearest enclosing let or universal frame, if any, or to the outermost level, otherwise. Thus, in our machine representation of stacks, where rules S-Ex-1 to S-Ex-4 are applied in an eager fashion, every universal frame carries a list of the type variables that are existentially bound immediately after it, and integer ranks count not only let frames, but also universal frames.

The solver's specification is extended with the rules in Figure 1-16. SSolve-All, a forward rule, discovers a universal constraint and enters it, creating a new universal frame to record its existence. S-ALLEx exploits Lemma 1.10.4 to hoist existential quantifiers out of the universal frame. It is analogous to S-LETALL, and its implementation may rely upon the same procedure (Exercise 1.8.8). The next two rules detect failure conditions. SALL-FAIL-1 states that the constraint $\forall \mathrm{X} . \exists \overline{\mathrm{Y}} . U$ is false if the rigid variable $\mathrm{X}$ is directly or indirectly dominated by a free variable $\mathrm{Z}$. Indeed, the value of $\mathrm{X}$ is then determined by that of $\mathrm{Z}$-but a universally quantified variable ranges over all values, so this is a contradiction. In such a case, $\mathrm{X}$ is commonly said to escape its scope. S-ALL-FAIL-2 states that the same constraint is false if $\mathrm{X}$ is equated with a nonvariable term. Indeed, the value of $\mathrm{X}$ is then
partially determined, since its head constructor is known, which again contradicts its universal status. Last, S-POP-ALL splits the current unification constraint into two components $U_{1}$ and $U_{2}$, where $U_{1}$ is made up entirely of old variables and $U_{2}$ constrains young variables only. This decomposition is analogous to that performed by S-POP-LET. Then, it is not difficult to check that $\forall \overline{\mathrm{X}} . \exists \overline{\mathrm{Y}}$. $\left(U_{1} \wedge U_{2}\right)$ is equivalent to $U_{1}$. So, the universal frame, as well as $U_{2}$, are discarded, and the solver proceeds by examining whatever remains on top of the stack $S$.

It is possible to further extend the treatment of universal frames with two rules analogous to S-COMPRESS and S-UNNAME. In practice, this improves the solver's efficiency, and makes it easier to share code between the treatment of let frames and that of universal frames.

It is interesting to remark that, as far as the underlying unification algorithm is concerned, there is no difference between existentially and universally quantified type variables. The algorithm solves whatever equations are presented to it, without inquiring about the status of their variables. Equations that lead to failure, because a rigid variable escapes its scope or is equated with a nonvariable term, are detected only when the universal frame is exited. A perhaps more common approach is to mark rigid variables as such, allowing the unification algorithm to signal failure as soon as one of the two error conditions is encountered. In this approach, a rigid variable may successfully unify only with itself or with flexible variables fresher than itself. It is often called a Skolem constructor in the literature (Läufer and Odersky, 1994; Shields and Peyton Jones, 2002). An interesting variant of this approach appears in Dowek, Hardin, Kirchner and Pfenning's treatment of (higher-order) unification $(1995 ; 1998)$, where flexible variables are represented as ordinary variables, while rigid variables are encoded using De Bruijn indices.

The properties of our constraint solver are preserved by this extension: it is possible to prove that Lemmas 1.8.9, 1.8.10, and 1.8.11 remain valid.

\section*{Type annotations, continued}

In Section 1.9, we introduced the expression form ( $t: \exists \overline{\mathrm{X}} . \mathrm{T}$ ), allowing an expression $t$ to be annotated with a type $\mathrm{T}$ whose free variables $\overline{\mathrm{X}}$ are locally and existentially bound. It is now natural to introduce the symmetric expression form ( $\mathrm{t}: \forall \overline{\mathrm{X}} . \mathrm{T}$ ), where $\mathrm{T}$ has kind $\star, \overline{\mathrm{X}}$ is bound within $\mathrm{T}$, and $\overline{\mathrm{X}}$ contains $f t v(\mathrm{~T})$, as before. Its constraint generation rule is as follows:

$$
\llbracket(\mathrm{t}: \forall \overline{\mathrm{X}} \cdot \mathrm{T}): \mathrm{T}^{\prime} \rrbracket=\forall \overline{\mathrm{X}} \cdot \llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \exists \overline{\mathrm{X}} \cdot\left(\mathrm{T} \leq \mathrm{T}^{\prime}\right) \quad \text { provided } \overline{\mathrm{X}} \# f t v\left(\mathrm{t}, \mathrm{T}^{\prime}\right)
$$

The first conjunct requires $t$ to have type $T$ for all values of $\overline{\mathrm{X}}$. Here, the type variables $\overline{\mathrm{X}}$ are universally bound, as expected. The second conjunct requires
$\mathrm{T}^{\prime}$ to be some instance of the universal annotation $\forall \overline{\mathrm{X}}$.T. Since $\mathrm{T}^{\prime}$ is only a monotype, it seems difficult to think of another sensible way of constraining $\mathrm{T}^{\prime}$. For this reason, the type variables $\overline{\mathrm{X}}$ are still existentially bound in the second conjunct. This makes the interpretation of the universal quantifier in type annotations a bit more complex than that of the existential quantifier. For instance, when subtyping is interpreted as equality, the constraint generation rule may be read: a valid type for ( $\mathrm{t}: \forall \overline{\mathrm{X}} . \mathrm{T}$ ) is of the form $\mathrm{T}$, for some choice of the type variables $\overline{\mathrm{X}}$, provided $\mathrm{t}$ has type $\mathrm{T}$ for all choices of $\overline{\mathrm{X}}$.

We remark that ( $t: \forall \overline{\mathrm{X}} . \mathrm{T}$ ) must be a new expression form: it cannot be encoded by adding new constants to the calculus-whereas ( $t: \exists \bar{X} . T$ ) couldbecause none of the existing constraint generation rules produce universally quantified constraints. Like all type annotations, it has identity semantics.

What is the use of universal type annotations, compared with existential type annotations? When a type variable is existentially bound, the typechecker is free to assign it whatever value makes the program well-typed. As a result, the expressions $(\lambda z . z \hat{+} \hat{1}: \exists X . X \rightarrow X)$ and $(\lambda z . z: \exists X . X \rightarrow X)$ are both welltyped: $\mathrm{X}$ is assigned int in the former case, and remains undetermined in the latter. However, it is sometimes useful to be able to insist that an expression should be polymorphic. This effect is naturally achieved by using a universally bound type variable. Indeed, $(\lambda z \cdot z \hat{+} \hat{1}: \forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X})$ is ill-typed, because $\forall \mathrm{X} .(\mathrm{X}=$ int) is false, while ( $\lambda z \cdot z: \forall X . X \rightarrow X)$ is well-typed.

1.10.5 EXERCISE $[\star]$ : Write down the constraints $\exists z \cdot \llbracket(\lambda z \cdot z \hat{+} \hat{1}: \forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}): \mathrm{Z} \rrbracket$ and $\exists Z . \llbracket(\lambda z . z: \forall X . X \rightarrow X): z \rrbracket$, which tell whether these expressions are well-typed. Check that the former is false, while the latter is satisfiable.

A universal type annotation, as defined above, is nothing but a (closed) Damas-Milner type scheme. Thus, the new construct ( $t: \forall \overline{\mathrm{X}} . \mathrm{T}$ ) gives us the ability to ensure that the expression $t$ admits the type scheme $\forall \overline{\mathrm{X}}$.T. This feature is exploited at the module level in ML-the-programming-language, where it is necessary to check that the inferred type for a module component $t$ is more general than the type scheme $\mathrm{S}$ that appears in the module's signature. In our view, this process simply consists in ensuring that $(t: S)$ is well-typed.

In Section 1.9, we have pointed out that local (that is, closed) type annotations offer limited expressiveness, because they cannot share type variables. To lift this limitation, we have introduced the expression forms $\exists \overline{\mathrm{X}}$. $\mathrm{t}$ and ( $\mathrm{t}: \mathrm{T}$ ). The former binds the type variables $\overline{\mathrm{X}}$ within $t$, making them available for use in type annotations, and instructs the constraint generator to existentially quantify them at this point. The latter requires $t$ to have $T$. It is natural to proceed in the same manner in the case of universal type annotations. We now introduce the expression form $\forall \overline{\mathrm{X}}$.t, which also binds $\overline{\mathrm{X}}$ within $t$, but comes
with a different constraint generation rule:

$$
\llbracket \forall \overline{\mathrm{x}} . \mathrm{t}: \mathrm{T} \rrbracket=\forall \overline{\mathrm{X}} \cdot \exists \mathrm{Z} \cdot \llbracket \mathrm{t}: \mathrm{Z} \rrbracket \wedge \exists \overline{\mathrm{X}} \cdot \llbracket \mathrm{t}: \mathrm{T} \rrbracket \quad \text { provided } \overline{\mathrm{X}} \# f t v(\mathrm{~T}) \wedge \mathrm{Z} \notin f t v(\mathrm{t})
$$

This rule is a bit more complex than that associated with the expression form $\exists \bar{X}$.t. Again, this is due to the fact that we do not wish to overconstrain T. The first exercise below shows that a more naïve version of the rule does not yield the desired behavior. The second exercise shows that this version does. The third exercise clarifies an efficiency concern.

1.10.6 EXERCISE $[\star]$ : Assume that $\llbracket \forall \overline{\mathrm{X}} . \mathrm{t}: \mathrm{T} \rrbracket$ is defined as $\forall \overline{\mathrm{X}}$. $\llbracket \mathrm{t}: \mathrm{T} \rrbracket$, provided $\overline{\mathrm{X}} \# \operatorname{ftv}(\mathrm{T})$. Write down the constraint $\llbracket \forall \mathrm{X} .(\lambda \mathrm{z} \cdot \mathrm{z}: \mathrm{X} \rightarrow \mathrm{X}): \mathrm{Z} \rrbracket$. Can you describe its solutions? Does it have the intended meaning?

1.10.7 ExErcise $[\star \star]$ : Let $\overline{\mathrm{x}} \supseteq f t v(\mathrm{~T})$ and $\overline{\mathrm{x}} \# f t v(\mathrm{t})$. Check that the constraints $\llbracket(\mathrm{t}: \forall \overline{\mathrm{X}} . \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ and $\llbracket \forall \overline{\mathrm{X}} .(\mathrm{t}: \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ are equivalent. In other words, local universal type annotations may also be expressed in terms of the more complex constructs described above.

1.10.8 EXERCISE $[\star \star \star \star, \nrightarrow]$ : The constraint generation rule that appears above compromises the linear time and space complexity of constraint generation, because it duplicates the term $t$. It is possible to avoid this problem, but this requires a slight generalization of the constraint language. Let us write let $\mathrm{x}: \forall \underline{\underline{X}} \bar{Y}\left[C_{1}\right] . \mathrm{T}$ in $C_{2}$ for $\forall \overline{\mathrm{X}} . \exists \overline{\mathrm{Y}} . C_{1} \wedge$ def $\mathrm{x}: \forall \overline{\mathrm{X}} \overline{\mathrm{Y}}\left[C_{1}\right] . \mathrm{T}$ in $C_{2}$. In this extended let form, the underlined variables $\overline{\mathrm{x}}$ are interpreted as rigid, instead of flexible, while checking that $C_{1}$ is satisfiable. However, the type scheme associated with $\mathrm{x}$ is not affected. Check that the above constraint generation rule may now be written as follows:

$$
\llbracket \forall \overline{\mathrm{X}} . \mathrm{t}: \mathrm{T} \rrbracket=\text { let } \mathrm{x}: \forall \underline{\mathrm{x}} \mathrm{z}[\llbracket \mathrm{t}: \mathrm{Z} \rrbracket] . \mathrm{Z} \text { in } \mathrm{x} \preceq \mathrm{T} \quad \text { provided } \mathrm{Z} \notin f t v(\mathrm{t})
$$

Roughly speaking, the new rule forms a most general type scheme for $t$, ensures that the type variables $\overline{\mathrm{X}}$ are unconstrained in it, and checks that $\mathrm{T}$ is an instance of it. Furthermore, it does not duplicate t. To complete the exercise, extend the specification of the constraint solver (Figures 1-12 and 116), as well as its implementation, to deal with this extension of the constraint language.

To conclude, let us once again stress that, if $\mathrm{T}$ has free type variables, the effect of the type annotation ( $\mathrm{t}: \mathrm{T}$ ) depends on how and where they are bound. The effect of how stems from the fact that binding a type variable universally, rather than existentially, leads to a stricter constraint. Indeed, we let the reader check that $\llbracket \forall \overline{\mathrm{X}} . \mathrm{t}: \mathrm{T} \rrbracket$ entails $\llbracket \exists \overline{\mathrm{X}} . \mathrm{t}: \mathrm{T} \rrbracket$, while the converse
does not hold in general. The effect of where has been illustrated, in the case of existentially bound type variables, in Section 1.9. It is due, in that case, to the fact that let and $\exists$ do not commute. In the case of universally bound type variables, it may be imputed to the fact that $\forall$ and $\exists$ do not commute. For instance, $\lambda \mathrm{z} . \forall \mathrm{X} .(\mathrm{z}: \mathrm{x})$ is ill-typed, because inside the $\lambda$-abstraction, the program variable $\mathrm{z}$ cannot be said to have every type. However, $\forall \mathrm{X} . \lambda \mathrm{z} .(\mathrm{z}: \mathrm{X})$ is well-typed, because the identity function does have type $\mathrm{X} \rightarrow \mathrm{X}$ for every $\mathrm{X}$.

1.10.9 EXERCISE $[\star]$ : Write down the constraints $\exists Z . \llbracket \lambda z . \forall x .(z: x): z \rrbracket$ and $\exists Z . \llbracket \forall \mathrm{x} . \lambda \mathrm{z} .(\mathrm{z}: \mathrm{X}): \mathrm{Z} \rrbracket$, which tell whether these expressions are well-typed. Is the former satisfiable? Is the latter?

In Standard ML and Objective Caml, the type variables that appear in type annotations are implicitly bound. That is, there is no syntax in the language for the constructs $\exists \bar{X}$. $t$ and $\forall \bar{x}$.t. When a type annotation ( $t: T$ ) contains a free type variable $\mathrm{X}$, a fixed convention tells how and where $\mathrm{X}$ is bound. In Standard ML, $\mathrm{X}$ is universally bound at the nearest val binding that encloses all related occurrences of X (Milner, Tofte, and Harper, 1990). The 1997 revision of Standard ML (Milner, Tofte, Harper, and MacQueen, 1997b) slightly improves on this situation by allowing type variables to be explicitly introduced at val bindings. However, they still must be universally bound. In Objective Caml, $\mathrm{X}$ is existentially bound at the nearest enclosing toplevel let binding; this behavior seems to be presently undocumented. We argue that (i) allowing type variables to be implicitly introduced is confusing; and (ii) for expressiveness, both universal and existential quantifiers should be made available to programmers. Surprisingly, these language design and type inference issues seem to have received little attention in the literature, although they have most likely been "folklore" for a long time. Peyton Jones and Shields (2003) study these issues in the context of Haskell, and concur with (i). Concerning (ii), they seem to think that the language designer must choose between existential and universal type variable introduction formswhich they refer to as "type-sharing" and "type-lambda"-whereas we point out that they may and should coexist.

\section*{Polymorphic recursion}

Example 1.2.10 explains how the letrec construct found in ML-theprogramming-language may be viewed as an application of the constant fix, wrapped inside a normal let construct. Exercise 1.9.6 shows that this gives rise to a somewhat restrictive constraint generation rule: generalization occurs only after the application of fix is typechecked. In other words, in letrec $f=\lambda$ z.t $_{1}$ in $t_{2}$, all occurrences of $f$ within $t_{1}$ must have the same
(monomorphic) type. This restriction is sometimes a nuisance, and seems unwarranted: if the function that is being defined is polymorphic, it should be possible to use it at different types even inside its own definition. Indeed, Mycroft (1984) extended Damas and Milner's type system with a more liberal treatment of recursion, commonly known as polymorphic recursion. The idea is to only request occurrences of $f$ within $t_{1}$ to have the same type scheme. Hence, they may have different types, all of which are instances of a common type scheme. It was later shown that well-typedness in Mycroft's extended type system is undecidable (Henglein, 1993; Kfoury, Tiuryn, and Urzyczyn, 1993). To work around this stumbling block, one solution is to use a semialgorithm, falling back to monomorphic recursion if it does not succeed or fail in reasonable time. Although such a solution might be appealing in the setting of an automated program analysis, it is less so in the setting of a programmer-visible type system, because it may become difficult to understand why a program is ill-typed. Thus, we describe a simpler solution, which consists in requiring the programmer to explicitly supply a type scheme for f. This is an instance of a mandatory type annotation.

To begin, we must change the status of fix, because if fix remains a constant, then $f$ must remain $\lambda$-bound and cannot receive a polymorphic type scheme. We turn fix into a language construct, which binds a program variable $f$, and annotates it with a DM type scheme. The syntax of values and expressions is thus extended as follows:

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-113.jpg?height=56&width=801&top_left_y=1202&top_left_x=742)

Please note that $f$ is bound within $\lambda$ z.t. The operational semantics is extended as follows.

$$
\begin{equation*}
(f i x f: S . \lambda z . t) v \longrightarrow(\text { let } f=f i x f: S . \lambda z . t \text { in } \lambda z . t) v \tag{R-FIX'}
\end{equation*}
$$

The type annotation $\mathrm{S}$ plays no essential role in the reduction; it is merely preserved. It is now possible to define letrec $\mathrm{f}: \mathrm{S}=\lambda \mathrm{z}_{\mathrm{t}} \mathrm{t}_{1}$ in $\mathrm{t}_{2}$ as syntactic sugar for let $f=f i x f: S . \lambda z . t_{1}$ in $t_{2}$.

We now give a constraint generation rule for fix:

$$
\llbracket f i x f: S . \lambda z . t: T \rrbracket=\text { let } f: S \text { in } \llbracket \lambda z . t: S \rrbracket \wedge S \preceq T
$$

The left-hand conjunct requires the function $\lambda z$.t to have type scheme $S$, under the assumption that $f$ has type $S$. Thus, it is now possible for different occurrences of $f$ within $t$ to receive different types. If $S$ is $\forall \bar{X}$. $T$, where $\overline{\mathrm{X}} \# \mathrm{ftv}(\mathrm{t})$, then we write $\llbracket t: S \rrbracket$ for $\forall \bar{X}$. $\llbracket t: T \rrbracket$. Indeed, checking the validity of a polymorphic type annotation-be it mandatory, as is the case here, or optional, as was previously the case-requires a universally quantified constraint. The right-hand conjunct merely constrains $\mathrm{T}$ to be an instance of $\mathrm{S}$.

Given the definition of letrec $f: S=\lambda z \cdot t_{1}$ in $t_{2}$ as syntactic sugar, the above rule leads to the following derived constraint generation rule for letrec:

$\llbracket$ letrec $f: S=\lambda$ z.t $t_{1}$ in $t_{2}: T \rrbracket=$ let $f: S$ in $\left(\llbracket \lambda z . t_{1}: S \rrbracket \wedge \llbracket t_{2}: T \rrbracket\right)$

This rule is arguably quite natural. The program variable $f$ is assigned the type scheme $S$ throughout its scope, that is, both inside and outside of the function's definition. The function $\lambda$ z.t $_{1}$ must itself have type scheme $\mathrm{S}$. Last, $\mathrm{t}_{2}$ must have type $\mathrm{T}$, as in every let construct.

1.10.10 EXERCISE $[\star \star]$ : Prove that the derived constraint generation rule above is indeed valid.

It is straightforward to prove that the extended language still enjoys subject reduction. The proof relies on the following lemma: if $t$ has type scheme $S$, then every instance of $S$ is also a valid type for $t$.

1.10.11 Lemma: $\llbracket \mathrm{t}: \mathrm{S} \rrbracket \wedge \mathrm{S} \preceq \mathrm{T} \Vdash \llbracket \mathrm{t}: \mathrm{T} \rrbracket$.

1.10.12 Theorem [SubJect Reduction]: (R-Fix') $\subseteq(\sqsubseteq)$.

The programming language Haskell (Hudak, Peyton Jones, Wadler, Boutel, Fairbairn, Fasel, Guzman, Hammond, Hughes, Johnsson, Kieburtz, Nikhil, Partain, and Peterson, 1992) offers polymorphic recursion. Interesting details about its typing rules may be found in (Jones, 1999).

It is worth pointing out that some restricted instances of type inference in the presence of polymorphic recursion are decidable. This is typically the case in certain program analyses, where a type derivation for the program is already available, and the goal is only to infer extra atomic annotations, such as binding time or strictness properties. Several papers that exploit this idea are (Dussart, Henglein, and Mossin, 1995a; Jensen, 1998; Rehof and Fähndrich, 2001).

\section*{Universal types}

ML-the-type-system enforces a strict stratification between types and type schemes, or, in other words, allows only prenex universal quantifiers inside types. We have pointed out earlier that there is good reason to do so: type inference for ML-the-type-system is decidable, while type inference for System $\mathrm{F}$, which has no such restriction, is undecidable. Yet, this restriction comes at a cost in expressiveness: it prevents higher-order functions from accepting polymorphic function arguments, and forbids storing polymorphic functions inside data structures. Fortunately, it is in fact possible to circumvent the problem by requiring the programmer to supply additional type information.

The approach that we are about to describe is reminiscent of the way algebraic data type definitions allow circumventing the problems associated with equirecursive types (Section 1.9). Because we do not wish to extend the syntax of types with universal types of the form $\forall \bar{Y}$.T, we instead allow universal type definitions, of the form

$$
\mathrm{D} \overrightarrow{\mathrm{X}} \approx \forall \overline{\mathrm{Y}} . \mathrm{T}
$$

where D still ranges over data types. If D has signature $\vec{\kappa} \Rightarrow \star$, then the type variables $\overrightarrow{\mathrm{X}}$ must have kind $\vec{\kappa}$. The type $\mathrm{T}$ must have kind $\star$. The type variables $\overline{\mathrm{X}}$ and $\overline{\mathrm{Y}}$ are considered bound within $\mathrm{T}$, and the definition must be closed, that is, $f t v(\mathrm{~T}) \subseteq \overline{\mathrm{X}} \overline{\mathrm{Y}}$ must hold. Last, the variance of the type constructor D must match its definition - a requirement stated as follows:

1.10.13 Definition: Let $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \forall \overline{\mathrm{Y}}$. $\mathrm{T}$ and $\mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \approx \forall \overline{\mathrm{Y}}^{\prime} \cdot \mathrm{T}^{\prime}$ be two $\alpha$-equivalent instances of a single universal type definition, such that $\overline{\mathrm{Y}} \# \operatorname{ftv}\left(\mathrm{T}^{\prime}\right)$ and $\overline{\mathrm{Y}}^{\prime} \# \operatorname{ftv}(\mathrm{T})$. Then, $\mathrm{D} \overrightarrow{\mathrm{X}} \leq \mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \Vdash \forall \overline{\mathrm{Y}}^{\prime} . \exists \overline{\mathrm{Y}} . \mathrm{T} \leq \mathrm{T}^{\prime}$ must hold.

This requirement is analogous to that found in Definition 1.9.8. The idea is, if $D \vec{X}$ and $D \vec{X}^{\prime}$ are comparable, then their unfoldings $\forall \bar{Y}$. $T$ and $\forall \bar{Y}^{\prime} \cdot T^{\prime}$ should be comparable as well. The comparison between them is expressed by the constraint $\forall \overline{\mathrm{Y}}^{\prime} . \exists \overline{\mathrm{Y}} . \mathrm{T} \leq \mathrm{T}^{\prime}$, which may be read: every instance of $\forall \overline{\mathrm{Y}}^{\prime} . \mathrm{T}^{\prime}$ is (a supertype of) an instance of $\forall \bar{Y}$.T. Again, when subtyping is interpreted as equality, the requirement of Definition 1.10 .13 is always satisfied; it becomes nontrivial only in the presence of true subtyping.

The effect of the universal type definition $D \vec{X} \approx \forall \bar{Y} . T$ is to enrich the programming language with a new construct:

$$
\mathrm{v}::=\ldots \mid \text { pack }_{\mathrm{D}} \mathrm{v} \quad \mathrm{t}::=\ldots \mid \text { pack }_{\mathrm{D}} \mathrm{t} \quad \mathcal{E}::=\ldots \mid \text { pack }_{\mathrm{D}} \mathcal{E}
$$

and with a new unary destructor open $\mathrm{D}_{\mathrm{D}}$. Their operational semantics is as follows:

$$
\begin{equation*}
\text { open }_{\mathrm{D}}\left(\operatorname{pack}_{\mathrm{D}} \mathrm{v}\right) \xrightarrow{\delta} \mathrm{v} \tag{R-OPEN-ALL}
\end{equation*}
$$

Intuitively, $\operatorname{pack}_{D}$ and open $_{D}$ are the two coercions that witness the isomorphism between $\mathrm{D} \overrightarrow{\mathrm{X}}$ and $\forall \overline{\mathrm{Y}}$.T. The value $\mathrm{pack}_{\mathrm{D}} \mathrm{v}$ behaves exactly like $\mathrm{v}$, except it is marked, as a hint to the typechecker. As a result, the mark must be removed using open $\mathrm{D}_{\mathrm{D}}$ before the value can be used.

What are the typing rules for pack $_{D}$ and open ${ }_{D}$ ? In System F, they would receive types $\forall \overline{\mathrm{X}} .(\forall \overline{\mathrm{Y}} . \mathrm{T}) \rightarrow \mathrm{D} \overrightarrow{\mathrm{X}}$ and $\forall \overline{\mathrm{X}}$.D $\overrightarrow{\mathrm{X}} \rightarrow \forall \overline{\mathrm{Y}}$.T, respectively. However, neither of these is a valid type scheme: both exhibit a universal quantifier under an arrow.

In the case of $\mathrm{pack}_{\mathrm{D}}$, which has been made a language construct rather than a constant, we work around the problem by embedding this universal
quantifier in the constraint generation rule:

$$
\llbracket \text { pack }_{\mathrm{D}} \mathrm{t}: \mathrm{T}^{\prime} \rrbracket=\exists \overline{\mathrm{X}} \cdot\left(\llbracket \mathrm{t}: \forall \overline{\mathrm{Y}} \cdot \mathrm{T} \rrbracket \wedge \mathrm{D} \overrightarrow{\mathrm{X}} \leq \mathrm{T}^{\prime}\right)
$$

The rule implicitly requires that $\overline{\mathrm{X}}$ be fresh for the left-hand side and that $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \forall \overline{\mathrm{Y}}$. $\mathrm{T}$ be (an $\alpha$-variant of) the definition of $\mathrm{D}$. The left-hand conjunct requires $t$ to have type scheme $\forall \bar{Y}$.T. The notation $\llbracket t ~: ~ S \rrbracket$ was defined on page 114. The right-hand conjunct states that a valid type for $\mathrm{pack}_{\mathrm{D}} \mathrm{t}$ is (a supertype of) D $\overrightarrow{\mathrm{X}}$.

We deal with open as follows. Provided $\overline{\mathrm{X}} \# \overline{\mathrm{Y}}$, we extend the initial environment $\Gamma_{0}$ with the binding open $\mathrm{D}_{\mathrm{D}}: \forall \overline{\mathrm{X}} \mathrm{Y} . \mathrm{D} \overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}$. We have simply hoisted the universal quantifier outside of the arrow - a valid isomorphism in System F.

The proof of the subject reduction theorem must be extended with the following new case:

1.10.14 Theorem [SUbJect Reduction]: (R-OPEn-AlL) $\subseteq(\sqsubseteq)$.

Proof: We have

$$
\begin{array}{ll} 
& \text { let } \Gamma_{0} \text { in } \llbracket \text { open }_{\mathrm{D}}\left(\text { pack }_{\mathrm{D}} \mathrm{v}\right): \mathrm{T}_{0} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{Z} .\left(\text { open }_{\mathrm{D}} \preceq \mathrm{Z} \rightarrow \mathrm{T}_{0} \wedge \llbracket \text { pack }_{\mathrm{D}} \mathrm{v}: \mathrm{Z} \rrbracket\right) \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{Z} \cdot\left(\exists \overline{\mathrm{X}}^{\prime} \overline{\mathrm{Y}}^{\prime} \cdot\left(\mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \rightarrow \mathrm{T}^{\prime} \leq \mathrm{Z} \rightarrow \mathrm{T}_{0}\right) \wedge \exists \overline{\mathrm{X}} \cdot(\llbracket \mathrm{v}: \forall \overline{\mathrm{Y}} . \mathrm{T} \rrbracket \wedge \mathrm{D} \overrightarrow{\mathrm{X}} \leq \mathrm{Z})\right) \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \overline{\mathrm{X}} \overline{\mathrm{X}}^{\prime} \overline{\mathrm{Y}}^{\prime} \cdot\left(\llbracket \mathrm{v}: \forall \overline{\mathrm{Y}} \cdot \mathrm{T} \rrbracket \wedge \mathrm{D} \overrightarrow{\mathrm{X}} \leq \mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \wedge \mathrm{T}^{\prime} \leq \mathrm{T}_{0}\right) \\
\Vdash & \text { let } \Gamma_{0} \text { in } \exists \overline{\mathrm{X}} \overline{\mathrm{X}}^{\prime} \overline{\mathrm{Y}}^{\prime} \cdot\left(\llbracket \mathrm{v}: \forall \overline{\mathrm{Y}} \cdot \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{T}^{\prime} \wedge \mathrm{T}^{\prime} \leq \mathrm{T}_{0}\right) \\
\Vdash & \text { let } \Gamma_{0} \text { in } \exists \overline{\mathrm{X}} \overline{\mathrm{Y}} \overline{\mathrm{X}}^{\prime} \overline{\mathrm{Y}}^{\prime} \cdot \llbracket \mathrm{v}: \mathrm{T}_{0} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \llbracket \mathrm{v}: \mathrm{T}_{0} \rrbracket \tag{6}
\end{array}
$$

where (1) is by definition of constraint generation for applications and for constants; $\mathrm{Z}$ is fresh; (2) is by definition of constraint generation for pack $_{\mathrm{D}}$ and open ${ }_{\mathrm{D}}$, where $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \forall \overline{\mathrm{Y}}$. $\mathrm{T}$ and $\mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \approx \forall \overline{\mathrm{Y}}^{\prime} . \mathrm{T}^{\prime}$ are two $\alpha$-equivalent instances of the definition of $\mathrm{D} ; \overline{\mathrm{X}}, \overline{\mathrm{Y}}, \overline{\mathrm{X}}^{\prime}$, and $\overline{\mathrm{Y}}^{\prime}$ are fresh and satisfy $\overline{\mathrm{Y}} \# \mathrm{ftv}\left(\mathrm{T}^{\prime}\right)$ and $\overline{\mathrm{Y}}^{\prime} \# \operatorname{ftv}(\mathrm{T}) ;(3)$ is by C-ExAnd, C-Arrow, and C-ExTrans, which allows eliminating Z; (4) is by Definition 1.10.13, Lemma 1.10.1, and C-ExAnd; (5) is by Lemmas 1.10 .11 and $1.6 .3 ;(6)$ is by C-Ex*.

The proof of $(\mathrm{R}-$ CONTEXT $) \subseteq(\sqsubseteq)$ must also be extended with a new subcase, corresponding the new production $\mathcal{E}::=\ldots \mid \operatorname{pack}_{\mathrm{D}} \mathcal{E}$. If the language is pure, this is straightforward. In the presence of side effects, however, this subcase fails, because universal and existential quantifiers in constraints do not commute. The problem is then avoided by restricting pack $_{\mathrm{D}}$ to values, as in Definition 1.7.7.

This approach to extending ML-the-type-system with universal (or existential - see below) types has been studied in (Läufer and Odersky, 1994;

Rémy, 1994; Odersky and Läufer, 1996; Shields and Peyton Jones, 2002). Laüfer and Odersky have suggested combining universal or existential type declarations with algebraic data type definitions. This allows suppressing the cumbersome pack $\mathrm{D}_{\mathrm{D}}$ and open $\mathrm{D}_{\mathrm{D}}$ constructs; instead, one simply uses the standard syntax for constructing and deconstructing variants and records.

\section*{Existential types}

Existential types (TAPL Chapter 24) are close cousins of universal types, and may be introduced into ML-the-type-system in the same manner. Actually, existential types have been introduced in ML-the-type-system before universal types. We give a brief description of this extension, insisting mainly on the differences with the case of universal types.

We now allow existential type definitions, of the form $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \exists \overline{\mathrm{Y}}$.T. The conditions required of a well-formed definition are unchanged, except the variance requirement, which is dual:

1.10.15 Definition: Let $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \exists \overline{\mathrm{Y}}$. $\mathrm{T}$ and $\mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \approx \exists \overline{\mathrm{Y}}^{\prime} \cdot \mathrm{T}^{\prime}$ be two $\alpha$-equivalent instances of a single existential type definition, such that $\overline{\mathrm{Y}} \# \operatorname{ftv}\left(\mathrm{T}^{\prime}\right)$ and $\overline{\mathrm{Y}}^{\prime} \# \operatorname{ftv}(\mathrm{T})$. Then, $\mathrm{D} \overrightarrow{\mathrm{X}} \leq \mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \Vdash \forall \overline{\mathrm{Y}} \cdot \exists \overline{\mathrm{Y}}^{\prime} . \mathrm{T} \leq \mathrm{T}^{\prime}$ must hold.

The effect of this existential type definition is to enrich the programming language with a new unary constructor pack $_{\mathrm{D}}$ and with a new construct: $t::=\ldots \mid$ open $_{\mathrm{D}} \mathrm{t} t$ and $\mathcal{E}::=\ldots\left|\operatorname{open}_{\mathrm{D}} \mathcal{E} \mathrm{t}\right| \operatorname{open}_{\mathrm{D}} \mathrm{v} \mathcal{E}$. Their operational semantics is as follows:

$$
\begin{equation*}
\text { open }_{\mathrm{D}}\left(\text { pack }_{\mathrm{D}} \mathrm{v}_{1}\right) \mathrm{v}_{2} \longrightarrow \mathrm{v}_{2} \mathrm{v}_{1} \tag{R-OPEN-Ex}
\end{equation*}
$$

In the literature, the second argument of open $\mathrm{D}_{\mathrm{D}}$ is often required to be a $\lambda$-abstraction $\lambda$ z.t, so the construct becomes open $_{D} t(\lambda z . t)$, often written open $_{D} t$ as $z$ in $t$.

Provided $\overline{\mathrm{X}} \# \overline{\mathrm{Y}}$, we extend the initial environment $\Gamma_{0}$ with the binding pack $_{D}: \forall \bar{X} \bar{Y} . T \rightarrow D \vec{X}$. The constraint generation rule for open ${ }_{D}$ is as follows:

$$
\llbracket \text { open }_{\mathrm{D}} \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime} \rrbracket=\exists \overline{\mathrm{X}} .\left(\llbracket \mathrm{t}_{1}: \mathrm{D} \overrightarrow{\mathrm{X}} \rrbracket \wedge \llbracket \mathrm{t}_{2}: \forall \overline{\mathrm{Y}} . \mathrm{T} \rightarrow \mathrm{T}^{\prime} \rrbracket\right)
$$

The rule implicitly requires that $\overline{\mathrm{X}}$ be fresh for the left-hand side, that $\overline{\mathrm{Y}}$ be fresh for $\mathrm{T}^{\prime}$, and that $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \forall \overline{\mathrm{Y}} . \mathrm{T}$ be (an $\alpha$-variant of) the definition of $\mathrm{D}$. The left-hand conjunct simply requires $t_{1}$ to have type $D \vec{X}$. The right-hand conjunct states that the function $t_{2}$ must be prepared to accept an argument of type $\mathrm{T}$, for any $\overline{\mathrm{Y}}$, and produce a result of the expected type $\mathrm{T}^{\prime}$. In other words, $t_{2}$ must be a polymorphic function.

The type scheme of existential pack ${ }_{D}$ resembles that of universal open $\mathrm{D}_{D}$, while the constraint generation rule for existential pen $_{D}$ is a close cousin
of that for universal pack $\mathrm{D}_{\mathrm{D}}$. Thus, the duality between universal and existential types is rather strong. The main difference lies in the fact that the existential open $\mathrm{D}_{\mathrm{D}}$ construct is binary, rather than unary, so as to limit the scope of the newly introduced type variables $\bar{Y}$. The duality may be better understood by studying the encoding of existential types in terms of universal types (Reynolds, 1983b).

As expected, R-OPEn-Ex preserves types.

1.10.16 Theorem [SubJect Reduction]: (R-OpEn-Ex) $\subseteq(\sqsubseteq)$.

1.10.17 ExERcise $[\star \star, \nrightarrow]$ : Prove Theorem 1.10.16. The proof is analogous, although not identical, to that of Theorem 1.10.14.

In the presence of side effects, the new production $\mathcal{E}::=\ldots \mid$ open $_{D}$ v $\mathcal{E}$ is problematic. The standard workaround is to restrict the second argument to open $_{D}$ to be a value.

\subsection*{1.11 Rows}

In Section 1.9, we have shown how to extend ML-the-programming-language with algebraic data types, that is, variant and record type definitions, which we now refer to as simple. This mechanism has a severe limitation: two distinct definitions must define incompatible types. As a result, one cannot hope to write code that uniformly operates over variants or records of different shapes, because the type of such code is not even expressible.

For instance, it is impossible to express the type of the polymorphic record access operation, which retrieves the value stored at a particular field $\ell$ inside a record, regardless of which other fields are present. Indeed, if the label $\ell$ appears with type $T$ in the definition of the simple record type $D \vec{X}$, then the associated record access operation has type $\forall \overline{\mathrm{X}}$.D $\overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}$. If $\ell$ appears with type $\mathrm{T}^{\prime}$ in the definition of another simple record type, say $\mathrm{D}^{\prime} \overrightarrow{\mathrm{X}}^{\prime}$, then the associated record access operation has type $\forall \overline{\mathrm{X}}^{\prime} . \mathrm{D}^{\prime} \overrightarrow{\mathrm{X}}^{\prime} \rightarrow \mathrm{T}^{\prime}$; and so on. The most precise type scheme that subsumes all of these incomparable type schemes is $\forall \mathrm{XY} . \mathrm{X} \rightarrow \mathrm{Y}$. It is, however, not a sound type scheme for the record access operation. Another powerful operation whose type is currently not expressible is polymorphic record extension, which copies a record and stores a value at field $\ell$ in the copy, possibly creating the field if it did not previously exist, again regardless of which other fields are present. (If $\ell$ was known to previously exist, the operation is known as polymorphic record update.)

In order to assign types to polymorphic record operations, we must do away with record type definitions: we must replace named record types, such as D $\overrightarrow{\mathrm{X}}$, with structural record types that provide a direct description of the record's
domain and contents. (Following the analogy between a record and a partial function from labels to values, we use the word domain to refer to the set of fields that are defined in a record.) For instance, a product type is structural: the type $T_{1} \times T_{2}$ is the (undeclared) type of pairs whose first component has type $\mathrm{T}_{1}$ and whose second component has type $\mathrm{T}_{2}$. Thus, we wish to design record types that behave very much like product types. In doing so, we face two orthogonal difficulties. First, as opposed to pairs, records may have different domains. Because the type system must statically ensure that no undefined field is accessed, information about a record's domain must be made part of its type. Second, because we suppress record type definitions, labels must now be predefined. However, for efficiency and modularity reasons, it is impossible to explicitly list every label in existence in every record type.

In what follows, we explain how to address the first difficulty in the simple setting of a finite set of labels. Then, we introduce rows, which allow dealing with an infinite set of labels, and address the second difficulty. We define the syntax and logical interpretation of rows, study the new constraint equivalence laws that arise in their presence, and extend the first-order unification algorithm with support for rows. Then, we review several applications of rows, including polymorphic operations on records, variants, and objects, and discuss alternatives to rows.

\section*{Records with finite carrier}

Let us temporarily assume that $\mathcal{L}$ is finite. In fact, for the sake of definiteness, let us assume that $\mathcal{L}$ is $\left\{\ell_{a}, \ell_{b}, \ell_{c}\right\}$.

To begin, let us consider only full records, whose domain is exactly $\mathcal{L}$-in other words, tuples indexed by $\mathcal{L}$. To describe them, it is natural to introduce a type constructor record of signature $\star \otimes \star \otimes \star \Rightarrow \star$. The type record $\mathrm{T}_{a} \mathrm{~T}_{b} \mathrm{~T}_{c}$ represents all records where the field $\ell_{a}$ (resp. $\ell_{b}, \ell_{c}$ ) contains a value of type $\mathrm{T}_{a}$ (resp. $\mathrm{T}_{b}, \mathrm{~T}_{c}$ ). Please note that record is nothing but a product type constructor of arity 3 . The basic operations on records, namely creation of a record out of a default value, which is stored into every field, update of a particular field (say, $\ell_{b}$ ), and access to a particular field (say, $\ell_{b}$ ), may be assigned the following type schemes:

$$
\begin{aligned}
\{\cdot\}: & \forall \mathrm{X} . \mathrm{X} \rightarrow \text { record } \mathrm{X} \mathrm{X} \mathrm{X} \\
\left\{\cdot \text { with } \ell_{b}=\cdot\right\}: & \forall \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{b}^{\prime} \mathrm{X}_{c} \cdot \text { record } \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{c} \rightarrow \mathrm{X}_{b}^{\prime} \rightarrow \text { record } \mathrm{X}_{a} \mathrm{X}_{b}^{\prime} \mathrm{X}_{c} \\
\cdot\left\{\ell_{b}\right\}: & \forall \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{c} \cdot \text { record } \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{c} \rightarrow \mathrm{X}_{b}
\end{aligned}
$$

Here, polymorphism allows updating or accessing a field without knowledge of the types of the other fields. This flexibility is made possible by the property that all record types are formed using a single record type constructor.

This is fine, but in general, the domain of a record is not necessarily $\mathcal{L}$ : it may be a subset of $\mathcal{L}$. How may we deal with this fact, while maintaining the above key property? A naïve approach consists in encoding arbitrary records in terms of full records, using the standard algebraic data type option, whose definition is option $\mathrm{X} \approx$ pre $\mathrm{X}+$ abs. We use pre for present and abs for absent: indeed, a field that is defined with value $\mathrm{v}$ is encoded as a field with value pre $\mathrm{v}$, while an undefined field is encoded as a field with value abs. Thus, an arbitrary record whose fields, if present, have types $\mathrm{T}_{a}, \mathrm{~T}_{b}$, and $\mathrm{T}_{c}$, respectively, may be encoded as a full record of type record (option $\mathrm{T}_{a}$ ) (option $\mathrm{T}_{b}$ ) (option $\mathrm{T}_{c}$ ). This naive approach suffers from a serious drawback: record types still contain no domain information. As a result, field access must involve a dynamic check, so as to determine whether the desired field is present: in our encoding, this corresponds to the use of case option .

To avoid this overhead and increase programming safety, we must move this check from runtime to compile time. In other words, we must make the type system aware of the difference between pre and abs. To do so, we replace the definition of option by two separate algebraic data type definitions, namely pre $\mathrm{X} \approx$ pre $\mathrm{X}$ and abs $\approx$ abs. In other words, we introduce a unary type constructor pre, whose only associated data constructor is pre, and a nullary type constructor abs, whose only associated data constructor is abs. Record types now contain domain information: for instance, a record of type record abs (pre $\mathrm{T}_{b}$ ) (pre $\mathrm{T}_{c}$ ) must have domain $\left\{\ell_{b}, \ell_{c}\right\}$. Thus, the type of a field tells whether it is defined. Since the type pre has no data constructors other than pre, the accessor pre ${ }^{-1}$, whose type is $\forall \mathrm{X}$.pre $\mathrm{X} \rightarrow \mathrm{X}$, and which allows retrieving the value stored in a field, cannot fail. Thus, the dynamic check has been eliminated.

To complete the definition of our encoding, we now define operations on arbitrary records in terms of operations on full records. To distinguish between the two, we write the former with angle braces, instead of curly braces. The empty record \langle\rangle , where all fields are undefined, may be defined as $\{$ abs $\}$. Extension at a particular field (say, $\left.\ell_{b}\right)\left\langle\cdot\right.$ with $\left.\ell_{b}=\cdot\right\rangle$ is defined as $\lambda r . \lambda z .\left\{r\right.$ with $\ell_{b}=$ pre $\left.z\right\}$. Access at a particular field (say, $\left.\ell_{b}\right) \cdot\left\langle\ell_{b}\right\rangle$ is defined as $\lambda$ z.pre ${ }^{-1} z .\left\{\ell_{b}\right\}$. It is straightforward to check that these operations have the following principal type schemes:

$$
\begin{aligned}
\langle\rangle: & \text { record abs abs abs } \\
\left\langle\cdot \text { with } \ell_{b}=\cdot\right\rangle: & \forall \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{b}^{\prime} \mathrm{X}_{c} \cdot \text { record } \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{c} \rightarrow \mathrm{X}_{b}^{\prime} \rightarrow \operatorname{record} \mathrm{X}_{a}\left(\text { pre } \mathrm{X}_{b}^{\prime}\right) \mathrm{X}_{c} \\
\cdot\left\langle\ell_{b}\right\rangle: & \forall \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{c} \text {.record } \mathrm{X}_{a}\left(\text { pre } \mathrm{X}_{b}\right) \mathrm{X}_{c} \rightarrow \mathrm{X}_{b}
\end{aligned}
$$

It is important to notice that the type schemes associated with extension and access at $\ell_{b}$ are polymorphic in $\mathrm{X}_{a}$ and $\mathrm{X}_{c}$, which now means that these operations are insensitive not only to the type, but also to the presence or
absence of the fields $\ell_{a}$ and $\ell_{c}$. Furthermore, extension is polymorphic in $\mathrm{X}_{b}$, which means that it is insensitive to the presence or absence of the field $\ell_{b}$ in its argument. The subterm pre $\mathrm{X}_{b}^{\prime}$ in its result type reflects the fact that $\ell_{b}$ is defined in the extended record. Conversely, the subterm pre $\mathrm{X}_{b}$ in the type of the access operation reflects the requirement that $\ell_{b}$ be defined in its argument.

Our encoding of arbitrary records in terms of full records was carried out for pedagogical purposes. In practice, no such encoding is necessary: the data constructors pre and abs have no machine representation, and the compiler is free to lay out records in memory in an efficient manner. The encoding is interesting, however, because it provides a natural way of introducing the type constructors pre and abs, which play an important role in our treatment of polymorphic record operations.

We remark that, in our encoding, the arguments of the type constructor record are expected to be either type variables or formed with pre or abs, while, conversely, the type constructors pre and abs are not intended to appear anywhere else. It is possible to enforce this invariant using kinds. In addition to $\star$, let us introduce the kind $\diamond$ of field types. Then, let us adopt the following signatures: pre: $\star \Rightarrow \diamond$, abs : $\diamond$, and record : $\diamond \otimes \diamond \otimes \diamond \Rightarrow \star$.

1.11.1 Exercise [ $\star$, Recommended, $\rightarrow$ ]: Check that the three type schemes given above are well-kinded. What is the kind of each type variable?

1.11.2 Exercise $[\star \star$, Recommended, $\nrightarrow]$ : Our record types contain information about every field, regardless of whether it is defined: we encode definedness information within the type of each field, using the type constructors pre and abs. A perhaps more natural approach would be to introduce a family of record type constructors, indexed by the subsets of $\mathcal{L}$, so that the types of records with different domains are formed with different constructors. For instance, the empty record would have type \{\} ; a record that defines the field $\ell_{a}$ only would have a type of the form $\left\{\ell_{a}: \mathrm{T}_{a}\right\}$; a record that defines the fields $\ell_{b}$ and $\ell_{c}$ only would have a type of the form $\left\{\ell_{b}: \mathrm{T}_{b} ; \ell_{c}: \mathrm{T}_{c}\right\}$; and so on. Assuming that the type discipline is Damas and Milner's (that is, assuming an equalityonly syntactic model), would it be possible to assign satisfactory type schemes to polymorphic record access and extension? Would it help to equip record types with a nontrivial subtyping relation?

\section*{Records with infinite carrier}

Finite records are insufficient both from practical and theoretical points of view. In practice, the set of labels could become very large, making the type of every record as large as the set of labels itself, even if only a few labels are
actually defined. In principle, the set of labels could even be infinite. Actually, in modular programs the whole set of labels may not be known in advance, which amounts in some way to working with an infinite set of labels. Thus, records must be drawn from an infinite set of labels-whether their domains are finite or infinite. Still, we can restrict our attention to records that are almost constant, that is, records where only a finite number of fields differ. With this restriction, full records (defined everywhere) can always be built by giving explicit definitions for a finite number of fields and a default value for all other fields, as in the finite case. For instance, the record $\{\{\{$ false $\}$ with $\ell=1\}$ with $\ell^{\prime}=$ true $\}$ is the record equal to true on field $\ell^{\prime}$, to 1 on field $\ell$, and to false on any other field.

Types of records are functions from labels to types, called rows. However, for sake of generality, we use a unary type constructor, say $\Pi$, as an indirection between rows and record types. Moreover, we further restrict our attention to the case where rows are also almost constant. (The fact that the property holds for record values does not imply that it also holds for record types, for the default value of some record could have a polymorphic type, and one could wish to see each field with a different instance of this polymorphic type. So this is a true restriction, but a reasonable one.) Thus, rows can also be represented by giving explicit types for a finite number of fields and a default type for all other fields. We write $\partial \mathrm{T}$ the row whose type is $\mathrm{T}$ on every field, and $\left(\ell: \mathrm{T} ; \mathrm{T}^{\prime}\right)$ the row whose type is $\mathrm{T}$ on field $\ell$ and $\mathrm{T}^{\prime}$ on other fields. Formally, $\partial$ is a unary type constructor and $\ell$ is a family of binary type constructors, written with syntactic sugar $(\ell: \cdot ; \cdot)$. For example, $\Pi\left(\ell\right.$ : bool ; $\left(\ell^{\prime}\right.$ : int ; $\partial$ bool $\left.)\right)$ is a record type that describes records whose field $\ell$ carries a value of type bool, field $\ell^{\prime}$ carries a value of type int, and all other fields carry values of type bool. In fact, this is a sound type for the record defined above. In fact, the type $\Pi\left(\ell^{\prime}\right.$ : int ; $(\ell$ :bool ; $\partial$ bool $\left.)\right)$ should also be a sound type for this record, since the order in which fields are specified should not matter. We actually treat both types as equivalent. Furthermore, the row $(\ell:$ bool ; $\partial$ bool $)$, which stands for bool on field $\ell$ and $\partial$ bool everywhere else, must also be equivalent to $\partial$ bool, which stands for bool everywhere.

A record type may also contain type variables. For instance, the record $\lambda z .\{z\}$ that maps any value $\mathrm{v}$ to a record with the default value $\mathrm{v}$ has type $\mathrm{X} \rightarrow \Pi(\partial \mathrm{x})$. Projections of this record on any field will return a value of the same type $\mathrm{X}$. By comparison, the function that reads some field $\ell$ of its (record) argument has type $\Pi(\ell: X ; Y) \rightarrow X$ : this says that the argument must be a record where field $\ell$ has type $\mathrm{X}$ and other fields may have any type. Variable $\mathrm{Y}$ is called a row variable, since it can be instantiated to any row. For instance, Y can be instantiated to $\left(\ell^{\prime}:\right.$ int $\left.; \mathrm{Y}^{\prime}\right)$ and as a result this function can be applied to the record above. Conversely, the row $\partial \mathrm{x}$, which is equal to $\left(\ell^{\prime}: \mathrm{x} ; \mathrm{x}\right)$, can
only be instantiated to rows of the form $\partial \mathrm{T}$, which are equal to $\left(\ell^{\prime}: \mathrm{T} ; \mathrm{T}\right)$, that is, to constant rows.

\section*{Syntax of row types}

Let $\mathcal{L}$ be a denumerable collection of labels. We write $\ell . L$ for $\{\ell\} \uplus L$, which implies $\ell \notin L$. We first introduce kinds, so as to distinguish rows such as ( $\ell$ : int ; $\partial$ bool) from basic types, such as int or int $\rightarrow$ int.

1.11.3 DEFINITION [Row KinDs]: Let row kinds be composed of a particular kind Type and the collection of kinds $\operatorname{Row}(L)$ where $L$ ranges over finite subsets of $\mathcal{L}$. We use letter $s$ to range over row kinds.

Intuitively, a row of kind $\operatorname{Row}(L)$ is a function of domain $\mathcal{L} \backslash L$ to types. That is, $L$ specifies the set of labels that the row must not define. For instance, the (basic) type $\Pi(\ell$ : int ; $\mathrm{x})$ has kind Type, the row $(\ell$ : int ; $\mathrm{x})$ has kind $\operatorname{Row}(\emptyset)$ provided $\mathrm{X}$ has kind $\operatorname{Row}(\{\ell\})$.

To remain abstract the definition of rows is parameterized by a signature $\mathcal{S}_{0}$ for building basic types and a signature $\mathcal{S}_{1}$ for building rows. From those two signatures, we then define a new signature $\mathcal{S}$ that completely specifies the set of types. However, the signature $\mathcal{S}$ must superimposed row kinds on top of the (basic) kinds of the two input signatures $\mathcal{S}_{0}$ and $\mathcal{S}_{1}$. We use product signatures to enlighten this process. More precisely, we build a product signature from two signatures $K \Rightarrow \kappa$ and $K^{\prime} \Rightarrow \kappa^{\prime}$ with the following notations: we write $\kappa . \kappa^{\prime}$ for the pair $\left(\kappa, \kappa^{\prime}\right) ; K . \kappa$ for the mapping $(d \mapsto K(d) . \kappa)^{d \in \operatorname{dom}(K)} ;(K \Rightarrow \kappa) . \kappa^{\prime}$ for the kind signature $K . \kappa \Rightarrow \kappa . \kappa^{\prime}$; and symmetrically, we write $\kappa . K^{\prime}$ and $\kappa .\left(K^{\prime} \Rightarrow \kappa^{\prime}\right)$. The signature $\mathcal{S}$ reuses the same input type constructors as $\mathcal{S}_{0}$ and $\mathcal{S}_{1}$, but at different row kinds. We use superscripts to provide copies of type constructors at different kinds, and thus avoid overloading of kinds.

1.11.4 Definition [Row extension of a signature]: Let $\mathcal{S}_{0}$ and $\mathcal{S}_{1}$ be signatures where all symbols of $\mathcal{S}_{1}$ are unary. The row extension of $\mathcal{S}_{0}$ with $\mathcal{S}_{1}$ is the signature $\mathcal{S}$ defined as follows where $\kappa$ ranges over basic kinds (those used in $\mathcal{S}_{0}$ and $\mathcal{S}_{1}$ ) and $s$ ranges over row kinds:

\begin{tabular}{|c|l|l|}
\hline$F \in \operatorname{dom}(\mathcal{S})$ & Signature & Conditions \\
\hline$G^{s}$ & $(K \Rightarrow \kappa) . s$ & $(G: K \Rightarrow \kappa) \in \mathcal{S}_{0}$ \\
$H$ & K.Row $(\emptyset) \Rightarrow \kappa$. Type & $(H: K \Rightarrow \kappa) \in \mathcal{S}_{1}$ \\
$\partial^{\kappa, L}$ & $\kappa .($ Type $\Rightarrow \operatorname{Row}(L))$ & \\
$\ell^{\kappa, L}$ & $\kappa .($ Type $\otimes \operatorname{Row}(\ell . L) \Rightarrow \operatorname{Row}(L))$ & $\ell \notin L$ \\
\hline
\end{tabular}

We usually write $\ell^{\kappa, L}: \mathrm{t}_{1}$; $\mathrm{t}_{2}$ instead of $\ell^{\kappa, L} \mathrm{t}_{1} \mathrm{t}_{2}$ and let this symbol be right-associative. We often drop the superscripts of type constructors since,
for any type expression $\mathrm{T}$, superscripts can be unambiguously recovered from the kind of $\mathrm{T}$.

1.11.5 EXAmple: Let us assume there is a single basic kind $\star$ and that $\mathcal{S}_{1}$ contain a unique type constructor $\Pi$ (hence of kind $\star \Rightarrow \star$ ). An example of row type is $\mathrm{X}_{0} \rightarrow \Pi\left(\ell_{1}: G ;\left(\mathrm{Y} \rightarrow \partial \mathrm{x}_{0}\right)\right)$. With all superscripts annotations, this type is

$$
\mathrm{X}_{0} \rightarrow^{\star, \text { Type }} \Pi\left(\ell_{1}^{\star, \text { Row }(\emptyset)}: G^{\text {Type }} ;\left(\mathrm{Y} \rightarrow^{\star, \text { Row }\left(\left\{\ell_{1}\right\}\right)} \partial^{\star, \text { Row }\left(\left\{\ell_{1}\right\}\right)} \mathrm{X}_{0}\right)\right) .
$$

Intuitively, this is the type of a function that takes a value of type $\mathrm{X}_{0}$ and returns a record where field $\ell_{1}$ has type $G$ and all other fields are functions that given a value of an arbitrary type would returns a value of (the same) type $\mathrm{X}_{0}$. An instance of this type is $\mathrm{X}_{0} \rightarrow \Pi\left(\ell_{1}: G ;\left(\left(\ell_{2}: \mathrm{Y}_{2} ; \mathrm{Y}^{\prime}\right) \rightarrow\left(\ell_{2}: \mathrm{X}_{0} ; \partial \mathrm{X}_{0}\right)\right)\right)$, obtained by instantiating row variable $\mathrm{Y}$ and by expanding the constant row $\partial \mathrm{X}_{0}$. As shown below, this type is actually equivalent to $\mathrm{X}_{0} \rightarrow \Pi\left(\ell_{1}: G\right.$; $\left.\ell_{2}: \mathrm{Y}_{2} \rightarrow \mathrm{X}_{0} ;\left(\mathrm{Y}^{\prime} \rightarrow \partial \mathrm{X}_{0}\right)\right)$, by distributivity of type constructor $\rightarrow$ other type constructor $\ell_{2}$. Please, note again the difference between $\mathrm{Y}$, which is a row variable that can expand to different type variables on different labels, and $\partial \mathrm{X}$, which is a constant row that expands to the same type variable $\mathrm{X}$ on all labels.

1.11.6 EXAMPLE [ ILL-KINDED EXPRESSION ]: Under the assumptions of the previous example, the expression $\mathrm{X} \rightarrow \Pi(\mathrm{X})$ is not a row type, since variable $\mathrm{X}$ cannot simultaneously be of row kind Type and $\operatorname{Row}(\emptyset)$ as required by its two occurrences, from left to right respectively. The expression $\left(\ell: \mathrm{x} ; \ell: \mathrm{X}^{\prime} ; \mathrm{x}^{\prime \prime}\right)$ is also ill-kinded, for the inner expression $\left(\ell: \mathrm{X}^{\prime} ; \mathrm{X}^{\prime \prime}\right)$ of row kind $\operatorname{Row}(L)$ with $\ell \notin L$ cannot also have row kind $\operatorname{Row}(\{\ell\})$, as required by its occurrence in the whole expression. Indeed, row kinds prohibit multiple definitions of the same label, as well as using rows in place of basic types and conversely. Notice that $\Pi(\Pi(\mathrm{X}))$ is also ill-formed, since type constructors of $\mathcal{S}_{1}$ are not lifted to row kinds and thus cannot appear in rows, except under the type constructor $\partial$, hence as basic types.

1.11.7 EXERCISE $[\star \star \star, \nrightarrow]$ : Design an algorithm that infers superscripts of type constructors of a type expression from its kind. Can the kind of the expression be inferred as well? Can you give an algorithm to check that type expressions are well-kinded when both the superscripts of type constructors and the kinds of the whole type expressions are omitted?

\section*{Meaning of rows}

As mentioned above, a row of kind $\operatorname{Row}(L)$ stands for a function from $\mathcal{L} \backslash L$ to types. Actually, it is simpler to represent this function explicitly as an
infinitely branching tree in the model. For this purpose, we use a collection of constructors $L$ of (infinite but denumerable) arity $\mathcal{L} \backslash L$.

1.11.8 Definition [Row model]: Let $\mathcal{S}$ be the row extension of a signature $\mathcal{S}_{0}$ with a signature $\mathcal{S}_{1}$. Let $\mathcal{S}_{\mathcal{M}}$ be the following signature, where $\kappa$ ranges over basic kinds and $L$ ranges over finite subsets of $\mathcal{L}$ :

\begin{tabular}{|l|l|l|}
\hline$F \in \operatorname{dom}\left(\mathcal{S}_{\mathcal{M}}\right)$ & Signature & Conditions \\
\hline$G$ & $(K \Rightarrow \kappa)$. Type & $(G: K \Rightarrow \kappa) \in \mathcal{S}_{0}$ \\
$H$ & K.Row $(\emptyset) \Rightarrow \kappa$. Type & $(H: K \Rightarrow \kappa) \in \mathcal{S}_{1}$ \\
$L^{\kappa}$ & $\kappa .($ Type $\mathcal{L} \backslash L \Rightarrow \operatorname{Row}(L))$ & \\
\hline
\end{tabular}

Let $\mathcal{M}_{\kappa}$ consist of the regular trees $t$ built over the signature $\mathcal{S}_{\mathcal{M}}$ such that $t(\epsilon)$ has image kind $\kappa$. We interpret a type constructor $F$ of signature $K \Rightarrow \kappa . s$ as a function that maps $T \in \mathcal{M}_{K}$ to $t \in \mathcal{M}_{\kappa . s}$ defined by cases on $F$ and on the basic kind $\kappa$.

\begin{tabular}{|l|l|l|}
\hline$F \in \mathcal{S}$ & $t(\epsilon)$ & For $d \in \operatorname{dom}(K)$ and $\ell \in \mathcal{L} \backslash L, \ell \neq \ell_{0}$. \\
\hline$G^{\text {Type }}$ & $G$ & $t / d=T(d)$ \\
$H$ & $H$ & $t / 1=T(1)$ \\
$G^{\text {Row }(L)}$ & $L^{\kappa}$ & $t(\ell)=G \wedge t /(\ell \cdot d)=T(d) / \ell$ \\
$\partial^{\kappa, L}$ & $L^{\kappa}$ & $t / \ell=T(1)$ \\
$\ell_{0}^{\kappa, L}$ & $L^{\kappa}$ & $t / \ell_{0}=T(1) \wedge t / \ell=T(2) / \ell$ \\
\hline
\end{tabular}

In the presence of subtyping, we let type constructors $G$ and $H$ behave in $\mathcal{S}_{\mathcal{M}}$ as in $\mathcal{S}_{0}$ and $\mathcal{S}_{1}$ and type constructors $L^{\kappa}$ be isolated and covariant in every position. Models that define ground types and interpret type constructors in this manner are referred to as row models.

\section*{Reasoning with row types}

In this section, we assume a subtyping model. All reasoning principles also apply to the equality-only model, which is a subcase of the subtyping model.

The meaning of rows has been carefully defined so as to be independent of some syntactical choices. In particular, the order in which the types of significant fields have been declared leaves the meaning of rows unchanged. This is formally stated by the following Lemma.

1.11.9 Lemma: The equations of Figure 1-17 are equivalent to true.

Proof: Each equation can be considered independently. It suffices to see that any ground assignment $\phi$ sends both sides of the equation to the same element

$$
\begin{align*}
\left(\ell_{1}: \mathrm{T}_{1} ; \ell_{2}: \mathrm{T}_{2} ; \mathrm{T}_{3}\right) & =\left(\ell_{2}: \mathrm{T}_{2} ; \ell_{1}: \mathrm{T}_{1} ; \mathrm{T}_{3}\right)  \tag{C-Row-LL}\\
\partial \mathrm{T} & =(\ell: \mathrm{T} ; \partial \mathrm{T})  \tag{C-Row-DL}\\
\partial\left(G \mathrm{~T}_{1} \ldots \mathrm{T}_{n}\right) & =G \partial \mathrm{T}_{1} \ldots \partial \mathrm{T}_{n}  \tag{C-Row-DG}\\
G\left(\ell: \mathrm{T}_{1} ; \mathrm{T}_{1}^{\prime}\right) \ldots\left(\ell: \mathrm{T}_{n} ; \mathrm{T}_{n}^{\prime}\right) & =\left(\ell: G \mathrm{~T}_{1} \ldots \mathrm{T}_{n} ; G \mathrm{~T}_{1}^{\prime} \ldots \mathrm{T}_{n}^{\prime}\right) \tag{C-Row-GL}
\end{align*}
$$

\section*{Figure 1-17: Equational reasoning for row types.}

$$
\begin{aligned}
& \left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{T}_{1}^{\prime}\right)=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{T}_{2}^{\prime}\right) \equiv \exists \mathrm{X} \cdot\left(\mathrm{T}_{1}^{\prime}=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{X}\right) \wedge \mathrm{T}_{2}^{\prime}=\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{x}\right)\right) \\
& \text { if } \mathrm{X} \# \operatorname{ftv}\left(\mathrm{T}_{1}, \mathrm{~T}_{1}^{\prime}, \mathrm{T}_{2}, \mathrm{~T}_{2}^{\prime}\right) \wedge \ell_{1} \neq \ell_{2} \\
& \left(\ell: \mathrm{T} ; \mathrm{T}^{\prime}\right)=G \mathrm{~T}_{i}^{I} \equiv \exists\left(\mathrm{x}_{i}, \mathrm{X}_{i}^{\prime}\right)^{I} \cdot\left(\mathrm{T}=G \mathrm{X}_{i}^{I} \wedge \mathrm{T}^{\prime}=G \mathrm{X}_{i}^{\prime} \wedge \mathrm{T}_{i}=\left(\ell: \mathrm{x}_{i} ; \mathrm{X}_{i}^{\prime}\right)\right) \\
& \text { if }\left(\mathrm{X}_{i}, \mathrm{X}_{i}\right)^{I} \# f t v\left(\mathrm{~T}, \mathrm{~T}^{\prime}, \mathrm{T}_{i}^{I}\right) \\
& \text { (C-MuTE-LG) } \\
& \partial \mathrm{T}=G \mathrm{~T}_{i}^{I} \equiv \exists \mathrm{x}_{i}^{I} \cdot\left(\mathrm{T}=G \mathrm{x}_{i}^{I} \wedge\left(\mathrm{T}_{i}=\partial \mathrm{x}_{i}\right)^{I}\right) \\
& \text { if } \mathrm{X}_{i}^{I} \# \operatorname{ftv}\left(\mathrm{T}, \mathrm{T}_{i}^{I}\right) \\
& \partial \mathrm{T}=\left(\ell: \mathrm{T}^{\prime} ; \mathrm{T}^{\prime \prime}\right) \equiv \mathrm{T}=\mathrm{T}^{\prime} \wedge \partial \mathrm{T}=\mathrm{T}^{\prime \prime}
\end{aligned}
$$

\section*{Figure 1-18: Constraint equivalence laws for rows.}

in the model, which follows directly from the meaning of row types. Notice that this fact only depends on the semantics of types and not on the semantics of the subtyping predicate.

It follows from those equations that type constructors $\ell, \partial$, and $G$ are never isolated, each equation exhibiting a pair of compatible top symbols. Variances and incompatible pairs of type constructors depend on the signature $\mathcal{S}_{0} \uplus \mathcal{S}_{1}$. However, it is not difficult to see that type constructors $\partial$ and $\ell$ are logically covariant in all directions and that the logical variance of types constructors $G$ of $\operatorname{dom}\left(\mathcal{S}_{0} \uplus \mathcal{S}_{1}\right)$ correspond to their syntactic variance, which, in most cases, will allow the decomposition of equations with the same top symbols. Moreover, an equation between two terms whose top symbols form one of the four compatible pairs derived from the equations of Figure 1-17 holds only if immediate subexpressions can be "conciliated" in some way. There is a transformation quite similar to decomposition, called mutation, that mimics the equations for rows (Figure 1-17) and described by the rules of Figure 1-18. For sake of readability and conciseness, we write $\mathrm{T}_{i}^{I}$ instead of $\mathrm{T}_{i}^{i \in I}$.

1.11.10 Lemma [Mutation]: All equivalence laws in Figure 1-18 hold.

Proof:
- Case C-Mute-LL: Let X \# ftv( $\left.\mathrm{T}_{1}, \mathrm{~T}_{1}^{\prime}, \mathrm{T}_{2}, \mathrm{~T}_{2}^{\prime}\right)(\mathbf{1})$ and $\ell_{1} \neq \ell_{2}$. Let $\operatorname{Row}(L)$ be the row kind of this equation. Let $\phi$ be a ground assignment that validates the constraint $\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{T}_{1}^{\prime}\right)=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{T}_{2}^{\prime}\right)$. That is, $\phi$ sends all terms of the multi-equation to the same ground type $t$ of row kind $\operatorname{Row}(L)$. Moreover, the row-term semantics implies that $t$ satisfies $t(\epsilon)=L, t / \ell_{1}=\phi\left(\mathrm{T}_{1}\right)=$ $\phi\left(\mathrm{T}_{2}^{\prime}\right) / \ell_{1}, t / \ell_{2}=\phi\left(\mathrm{T}_{1}^{\prime}\right) / \ell_{2}=\phi\left(\mathrm{T}_{2}\right)$, and $t / \ell=\phi\left(\mathrm{T}_{2}^{\prime}\right) / \ell=\phi\left(\mathrm{T}_{1}^{\prime}\right) / \ell$ for all $\ell \in \mathcal{L} \backslash \ell_{1} \cdot \ell_{2} . L$ (2). Let $t^{\prime}$ be the tree defined by $t^{\prime}(\epsilon)=\ell_{1} \cdot \ell_{2} . L$ and $t^{\prime} / \ell=t / \ell$ for all $\ell \in \mathcal{L} \backslash \ell_{1} \cdot \ell_{2} . L$. By construction and (2), $\phi\left[\mathrm{X} \mapsto t^{\prime}\right]$ satisfies both equations $\mathrm{T}_{1}^{\prime}=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{x}\right)$ and $\mathrm{T}_{2}^{\prime}=\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{x}\right)$. Thus by CM-ExisTs and (1), $\phi$ satisfies $\exists \mathrm{X} \cdot \mathrm{T}_{1}^{\prime}=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{X}\right) \wedge \mathrm{T}_{2}^{\prime}=\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{X}\right)$. Conversely, we have the entailment:

$$
\begin{align*}
& \exists \mathrm{X} .\left(\mathrm{T}_{1}^{\prime}=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{X}\right) \wedge \mathrm{T}_{2}^{\prime}=\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{X}\right)\right) \\
& \equiv \exists \mathrm{X} .\left(\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{T}_{1}^{\prime}\right)=\left(\ell_{1}: \mathrm{T}_{1} ; \ell_{2}: \mathrm{T}_{2} ; \mathrm{X}\right) \wedge\right. \\
&\left.\quad\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{T}_{2}^{\prime}\right)=\left(\ell_{2}: \mathrm{T}_{2} ; \ell_{1}: \mathrm{T}_{1} ; \mathrm{X}\right)\right)  \tag{3}\\
& \Vdash \exists \mathrm{X} .\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{T}_{1}^{\prime}\right)=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{T}_{2}^{\prime}\right)  \tag{4}\\
& \equiv\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{T}_{1}^{\prime}\right)=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{T}_{2}^{\prime}\right) \tag{5}
\end{align*}
$$

(3) follows by covariance of $\ell_{1}$ and $\ell_{2}$; (4) by C-Row-LL and transitivity of equivalence; (5) by $\mathrm{C}-\mathrm{Ex} *$ and (1).
- Cases C-Mute-LG, C-Mute-DG, and C-Mute-DL: The reasoning is similar to the case C-Mute-LL.

\section*{Solving row constraints in an equality model}

In this section, we extend the constraint solver for the equality-only free tree model (Figure 1-11), so as to handle rows. We thus assume an equality-only model.

Mutation is a common technique to solve equations in a large class of nonfree algebras that are described by syntactic theories (Kirchner and Klay, 1990). The equations of Figure 1-17 happen to be a syntactic presentation of an equational theory, from which a unification algorithm could be automatically derived (Rémy, 1993). We recover the same transformation rules directly, without using results on syntactic theories.

The following lemma shows that all pairs of distinct type constructors for which there is no mutation rule are in fact incompatible.

1.11.11 Lemma: All symbols $H \in \mathcal{S}_{1}$ are isolated. Furthermore for every pair of distinct type constructors $G_{1}, G_{2} \in \operatorname{dom}\left(\mathcal{S}_{0} \uplus \mathcal{S}_{1}\right)$, and every row kind $s$, we have $G_{1}^{s} \bowtie G_{2}^{s}$.

Proof: Terms of the form $H \overrightarrow{\mathrm{T}}$ are interpreted by ground types with $H$ at occurrence $\epsilon$, and conversely the only interpretations of types with $H$ at occurrence $\epsilon$ are terms of the form $H \overrightarrow{\mathrm{T}}$. Hence, no ground assignment can ever

$$
\begin{aligned}
& \left(\ell_{1}: \mathrm{X}_{1} ; \mathrm{X}_{1}^{\prime}\right)=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{T}_{2}^{\prime}\right)=\epsilon \quad \rightarrow \quad \exists \mathrm{Y} .\left(\mathrm{X}_{1}^{\prime}=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{Y}\right) \wedge \mathrm{T}_{2}^{\prime}=\left(\ell_{1}: \mathrm{X}_{1} ; \mathrm{Y}\right)\right) \\
& \wedge\left(\ell_{1}: \mathrm{X}_{1} ; \mathrm{X}_{1}^{\prime}\right)=\epsilon \\
& \text { if } \mathrm{Y} \# \operatorname{ftv}\left(\mathrm{X}_{1}, \mathrm{X}_{1}^{\prime}, \mathrm{T}_{2}, \mathrm{~T}_{2}^{\prime}\right) \wedge \ell_{1} \neq \ell_{2} \\
& \left(\ell: \mathrm{X} ; \mathrm{X}^{\prime}\right)=G \mathrm{~T}_{i}^{i \in I}=\epsilon \quad \rightarrow \quad \exists\left(\mathrm{Y}_{i}, \mathrm{Y}_{i}^{\prime}\right)^{i \in I} \cdot\left(\mathrm{X}=G \mathrm{Y}_{i}^{i \in I} \wedge \mathrm{X}^{\prime}=G \mathrm{Y}_{i}^{\prime}{ }_{i}^{i \in I} \wedge \mathrm{T}_{i}=\left(\ell: \mathrm{Y}_{i} ; \mathrm{Y}_{i}^{\prime}\right)\right) \\
& \wedge\left(\ell: X ; X^{\prime}\right)=\epsilon \\
& \text { if }\left(\mathrm{Y}_{i}, \mathrm{Y}_{i}^{\prime}\right)^{i \in I} \# f t v\left(\mathrm{X}, \mathrm{X}^{\prime}, \mathrm{T}_{i}^{i \in I}\right) \\
& \partial \mathrm{X}=G \mathrm{~T}_{i}^{i \in I}=\epsilon \quad \rightarrow \quad \exists \mathrm{Y}_{i}^{i \in I} \cdot\left(\mathrm{X}=G \mathrm{Y}_{i}^{i \in I} \wedge\left(\mathrm{T}_{i}=\partial \mathrm{Y}_{i}\right)^{i \in I}\right) \\
& \wedge \partial \mathrm{x}=\epsilon \\
& \text { if } \mathrm{Y}_{i}^{i \in I} \# f t v\left(\mathrm{X}, \mathrm{T}_{i}^{i \in I}\right) \\
& \partial \mathrm{x}=\left(\ell: \mathrm{T} ; \mathrm{T}^{\prime}\right)=\epsilon \quad \rightarrow \quad \mathrm{X}=\mathrm{T} \wedge \partial \mathrm{x}=\mathrm{T}^{\prime} \wedge \partial \mathrm{x}=\epsilon \\
& G \overrightarrow{\mathrm{T}}=G^{\prime} \overrightarrow{\mathrm{T}}^{\prime}=\epsilon \rightarrow \text { false } \\
& \text { if } F \bowtie F^{\prime}
\end{aligned}
$$

\section*{Figure 1-19: Unification addendum for row types}

send $H \overrightarrow{\mathrm{T}}$ and $F \overrightarrow{\mathrm{T}^{\prime}}$ to the same ground term when $F \neq H$ and, as a result, $H$ is isolated.

Let $G_{1}$ and $G_{2}$ be two type constructors of $\mathcal{S}_{0}$. For $s=$ Type, the interpretations of terms of the form $G_{1}^{s} \overrightarrow{\mathrm{T}}$ and $G_{2}^{s} \overrightarrow{\mathrm{T}}^{\prime}$ are ground types with symbols $G_{1}$ and $G_{2}$ at occurrence $\epsilon$, respectively. Hence they cannot be made equal under any ground assignment. For $s=\operatorname{Row}(L)$, the interpretations of terms of the form $G_{1}^{s} \overrightarrow{\mathrm{T}}$ and $G_{2}^{s} \overrightarrow{\mathrm{T}}^{\prime}$ are ground types with constructor $L$ at occurrence $\epsilon$ and constructors $G_{1}$ and $G_{2}$ at occurrence 1, respectively. Hence they cannot be made equal under any ground assignment.

Any other combination of type constructors forms a compatible pair, as illustrated by equations of Figure 1-17 and can be transformed by mutation rules of Figure 1-18. The constraint solver for row-terms is the relation $\rightarrow^{\dagger}$ defined by the rewriting rules of Figure 1-11, except Rule S-CLASH, which is replaced by the set of rules of Figure 1-19.

1.11.12 Lemma: The rewriting system $\rightarrow^{\dagger}$ is strongly normalizing.

Please, note that the termination of $\rightarrow^{\dagger}$ relies on types being well-kinded. In particular, $\rightarrow^{\dagger}$ would not terminate on the ill-kinded system of equations $\mathrm{X}=\ell: \mathrm{T} ; \mathrm{X}^{\prime} \wedge \mathrm{X}^{\prime}=\ell^{\prime}: \mathrm{T} ; \mathrm{X}$.

1.11.13 Lemma: If $U \rightarrow^{\dagger} U^{\prime}$, then $U \equiv U^{\prime}$.

Proof: It suffices to check the property independently for each rule defining $\rightarrow^{\dagger}$. The proof for rules of Figure 1-11 but S-CLASH remain valid for row terms. For S-Decompose, it follows by the invariance of all type constructors, which is preserved for row terms. For rule S-CLASS-I it follows by Lemma 1.11.11 and for mutation rules, it follows by Lemma 1.11.10.

Although reductions $\rightarrow$ are not sound for row types, hence $\rightarrow$ cannot be used for computation over row types, it has some interest. In particular, the following property shows that normal forms for row types are identical to normal forms for regular types.

1.11.14 Lemma: A system $U$ in normal form for $\rightarrow^{\dagger}$ is also in normal form for $\rightarrow$.

Proof: The only rule of $\rightarrow$ that is not in $\rightarrow^{\dagger}$ is S-CLASH. Thus, it suffices to observe that if Rule S-CLASH would be applicable, then either Rule S-CLASS-I or a mutation rule would be applicable as well.

As a corollary, Lemma 1.8.6 extends to row types.

\section*{Operations on records}

We now illustrate the use of rows for typechecking operations on records. The simplest application of rows are full records with infinite carrier. Records types are expressed with rows instead of a simple product type. The basic operations are the same as in the finite case, that is, creation, polymorphic update, and polymorphic access, but labels are now taken from an infinite set. However, creation and polymorphic update, which where destructors are now taken as constructors and used to represent records as association lists. The access of a record $\mathrm{v}$ at a field $\ell$ is obtained by linearly searching $\mathrm{v}$ for a definition of field $\ell$ and returning this definition, or returning the default value if no definition has been found for $\ell$.

1.11.15 Example [Full Records]: We assume a unique basic kind $\star$ and a unique covariant isolated type constructor $\Pi$ in $\mathcal{S}_{1}$. Let $\{\cdot\}$ be a unary constructor, $(\{\cdot \text { with } \cdot=\ell\})^{\ell \in \mathcal{L}}$ a collection of binary constructors, and $(\ell .\{\cdot\})^{\ell \in \mathcal{L}}$ a collection of unary destructors with the following reduction rules:

$$
\begin{array}{rllr}
\{\mathrm{v}\} \cdot\{\ell\} & \xrightarrow{\delta} & \mathrm{v} & \\
\{\mathrm{w} \text { with } \ell=\mathrm{v}\} \cdot\{\ell\} & \xrightarrow{\delta} & \mathrm{v} & \\
\left\{\mathrm{w} \text { with } \ell^{\prime}=\mathrm{v}\right\} \cdot\{\ell\} & & \\
& \mathrm{w} .\{\ell\} & \text { if } \ell \neq \ell^{\prime} & \text { (RD-DEFAULT) } \\
\text { (RD-FOLLOw) }
\end{array}
$$

Let the initial environment $\Gamma_{0}$ contain the following bindings

$$
\begin{aligned}
\{\cdot\}: & \forall \mathrm{X} . \mathrm{X} \rightarrow \Pi(\partial \mathrm{X}) \\
\{\cdot \text { with } \ell=\cdot\}: & \forall \mathrm{XX} \mathrm{Y} . \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}^{\prime} \rightarrow \Pi\left(\ell: \mathrm{X}^{\prime} ; \mathrm{Y}\right) \\
\cdot\{\ell\}: & \forall \mathrm{XY} . \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}
\end{aligned}
$$

1.11.16 ExERcise [Full Records, $\star \star \star, \nrightarrow]$ : Check that these definitions meet the requirements of Definition 1.7.6.

1.11.17 ExErcise [Field Exchange, $\star \star$ ]: Add an operation to permute two fields of a record: give the reduction rules and the typing assumptions and check that the requirements of Definition 1.7.6 are preserved.

1.11.18 ExErcise [Normal forms For Records, $\star \star \star \star$ ]: Record values may contain repetitions. For instance, $\left\{\{\mathrm{w}\right.$ with $\ell=\mathrm{v}\}$ with $\left.\ell=\mathrm{v}^{\prime}\right\}$ is a value that is in fact observationally equivalent to $\left\{\mathrm{w}\right.$ with $\left.\ell=\mathrm{v}^{\prime}\right\}$. So are the two record values $\left\{\{\mathrm{w}\right.$ with $\ell=\mathrm{v}\}$ with $\left.\ell^{\prime}=\mathrm{v}^{\prime}\right\}$ and $\left\{\left\{\mathrm{w}\right.\right.$ with $\left.\ell^{\prime}=\mathrm{v}^{\prime}\right\}$ with $\left.\ell=\mathrm{v}\right\}$ when $\ell^{\prime} \neq \ell$. Modify the semantics, so that two record values of the same type have similar structure and records do not contain inaccessible values.

1.11.19 ExERcise [Map Apply, $\star \star$ ]: Add a binary operation map such that the expressions (map v $\mathrm{w}$ ). $\{\ell\}$ and v. $\{\ell\}$ w. $\{\ell\}$ reduce to the same value for every label $\ell$.

1.11.20 EXERCISE $[\star, \nrightarrow]$ : So far, full records are almost constants. This condition is not necessary for values, but only for types. As an example, introduce a primitive record, that is a nullary record constructor, that maps every label to a distinct integer. Give its typing assumption and review the semantics of records.

As opposed to full records, standard records are partial and their domains are finite (but with infinite carrier) and statically determined from their types. Standard records can be built by extending the empty record on a finite number of fields. We refer to such records as records with polymorphic extension. Record with polymorphic extension can be obtained by means of encoding into full records, much as in the finite case.

1.11.21 Example [Encoding of POLymorphic eXtension]: Reusing the two type definitions abs and pre that have introduced for the finite case, we let abs encodes an undefined field and prev encode a field with value v. We use the following syntactic sugar with their meaning and principal types:

$$
\begin{aligned}
& \langle\rangle \stackrel{\text { def }}{=}\{a b s\} \\
& : \Pi(\partial \mathrm{abs}) \\
& \langle\cdot \text { with } \ell=\cdot\rangle \stackrel{\text { def }}{=} \lambda \mathrm{v} \cdot \lambda \mathrm{w} \cdot\{\mathrm{w} \text { with } \ell=\text { pre } \mathrm{v}\} \\
& : \forall \mathrm{XX}^{\prime} \mathrm{Y} . \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}^{\prime} \rightarrow \Pi\left(\ell: \text { pre } \mathrm{X}^{\prime} ; \mathrm{Y}\right) \\
& \cdot\langle\ell\rangle \stackrel{\text { def }}{=} \lambda \mathrm{v} \cdot \mathrm{pre}^{-1}(\mathrm{v} \cdot\{\ell\}) \\
& : \forall \mathrm{XY} . \Pi(\ell: \text { pre } \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}
\end{aligned}
$$

1.11.22 ExERcise [Recommended, $\star$ ]: Extension may actually override an existing field. Can you define a version polymorphic extension that prevents this situation from happening? Add an operation that hide some particular field of a record.

Extensible records can also be implemented directly, without encoding into full records. In fact, this requires only a tiny variation on full records.

1.11.23 EXample [Records With Polymorphic eXtension]: Let $\star$ and $\diamond$ be two basic kinds. Let the basic signature $\mathcal{S}_{0}$ contain (in addition to $\rightarrow$ ) the covariant isolated type constructors pre of kind $\star \Rightarrow \diamond$ and abs of kind $\diamond$. In the presence of subtyping, we may assume pre $\leqslant$ abs. Let $\mathcal{S}_{1}$ contain the unique covariant isolated type constructor $\Pi$ of kind $\diamond \Rightarrow \star$. Let \langle\rangle be a unary constructor, $\left(\{\cdot \text { with } \cdot=\ell)^{\ell \in \mathcal{L}}\right.$ be a binary constructor, and $(\ell .\{\cdot\})^{\ell \in \mathcal{L}}$ be a unary destructor with the following reduction rules:

$$
\begin{aligned}
& \langle\mathrm{w} \text { with } \ell=\mathrm{v}\rangle .\langle\ell\rangle \quad \xrightarrow{\delta} \quad \mathrm{v} \quad \text { (ER-FOUnd) } \\
& \left\langle\text { w with } \ell^{\prime}=\mathrm{v}\right\rangle .\langle\ell\rangle \quad \xrightarrow{\delta} \quad \text { w. }\{\ell\} \quad \text { if } \ell \neq \ell^{\prime} \quad \text { (ER-FOLLOw) }
\end{aligned}
$$

Let $\Gamma_{0}$ contain the following typing assumptions:

$$
\begin{aligned}
\langle\rangle: & \Pi(\partial \mathrm{abs}) \\
\langle\cdot \text { with } \ell=\cdot\rangle & \forall \mathrm{XX} \mathrm{Y} . \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}^{\prime} \rightarrow \Pi\left(\ell: \text { pre } \mathrm{X}^{\prime} ; \mathrm{Y}\right) \\
\cdot\langle\ell\rangle: & \forall \mathrm{XY} . \Pi(\ell: \text { pre X } ; \mathrm{Y}) \rightarrow \mathrm{X}
\end{aligned}
$$

Notice that the typing assumptions obtained from the direct approach are identical to those obtained via the encoding into full records in Example 1.11.21.

1.11.24 EXERCISE $[\star \star \star \star, \nrightarrow]$ : Prove the equivalence between the direct semantics and the semantics via the encoding into records with a default.

1.11.25 Exercise [Recommended, $\star \star, \nrightarrow$ ]: Prove that type soundness for extensible records hold in both the subtyping model and equality-only models.

1.11.26 Exercise [Recommended, $\star, \nrightarrow$ ]: Check that in the subtyping a record with more fields can be used in place of records with fewer fields. Check that this is not the case in the equality-only model.

1.11.27 EXAMPLE [REFINEMENT OF RECORD TYPES]: In an equality-only model, records with more fields cannot be used in place of records with fewer fields. However, this may be partially recovered by a small refinement of the structure of types. The presence of fields can actually be split form their types, thus enabling some polymorphism over the presence of fields while type of fields themselves remains fixed. Let o be a new basic kind. Let type constructors abs and pre be both of kind $\circ$ and let $\cdot$ be a new type constructor of kind $\circ \otimes \star \Rightarrow \diamond$. Let $\Gamma_{0}$ contain the following typing assumptions:

$$
\begin{aligned}
\langle\rangle: & \forall \mathrm{X} . \Pi(\partial(\text { abs } \cdot \mathrm{X})) \\
\langle\cdot \text { with } \ell=\cdot\rangle: & \forall \mathrm{ZXX}^{\prime} \mathrm{Y} . \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}^{\prime} \rightarrow \Pi\left(\ell: \mathrm{Z} \cdot \mathrm{X}^{\prime} ; \mathrm{Y}\right) \\
\cdot\langle\ell\rangle: & \forall \mathrm{XY} . \Pi(\ell: \operatorname{pre} \cdot \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}
\end{aligned}
$$

The semantics of records remain unchanged. The new signature strictly generalizes the previous one (strictly more programs can be typed) while preserving type soundness. Here is a program that can now be typed and that could not be typed before:

$$
\text { (if } a \text { then }\left\langle\left\langle\langle\rangle \text { with } \ell^{\prime}=\text { true) with } \ell=1\right\rangle \text { else }\langle\langle\rangle \text { with } \ell=2\rangle \text { ). }\langle\ell\rangle\right.
$$

Notice however, that when a present field is forgotten, the type of the field is not. Therefore two records defining the same field but with incompatible types can still not be mixed, which is possible in the subtyping model.

1.11.28 EXAmple [REFINED SUbTypIng]: The previous refinement for an equalityonly model is not much interesting in the case of a subtyping model.

The subtyping assumption pre $\leqslant$ abs makes abs play the role of $T$ for fields. That is, abs encodes the absence of information and not the information of absence. In other words, a value whose field $\ell$ has type abs may either be undefined or defined on field $\ell$; in the latter case, the fact that field $\ell$ is actually defined has just been forgotten. Thus, types only provides a lower approximation of the actual domain of records. This is a lost of accuracy by comparison with the equality-only model, where a record domain is known from its type. As a result, some optimizations in the representation of records that are only possible when the exact domain of a record is statically known are lost.

Fortunately, there is a way to recover such accuracy. A conservative solution could of course to drop the inequality pre $\leqslant$ abs. Notice that this would still be more expressive than using an equality model since, for instance $\Pi(\ell$ : pre $\left.\left(\mathrm{T}_{1} \rightarrow \mathrm{T}_{2}\right) ; \mathrm{T}\right) \leq \Pi(\ell$ : pre $\top ; \mathrm{T})$ would still hold, as long as $\rightarrow \leq \top$ does hold. This solution is known as depth-only subtyping for records, while the previous one provided both depth and width record subtyping. Conversely, one could also keep width subtyping and disallow depth subtyping, by preserving
the relation pre $\leqslant$ abs while requiring pre to be invariant; in this case, presence of fields can be forgotten as a whole, but the types of fields cannot be weakened as long as fields remain visible.

Another more interesting solution consists in introducing another type constructor either of signature $\diamond$ and assuming that pre $\leqslant$ either and abs $\leqslant$ either (but pre $\nless$ abs). Here, either plays the role of $T$ for fields and means either present (and forgotten) or absent. while abs really means absent. The accuracy of typechecking can be formally stated as the fact that a record value of type $\Pi(\ell$ : abs $; \mathrm{T})$ cannot define field $\ell$.

1.11.29 Example [miXed subtyping]: It is tempting to mix all variations of Example 1.11.28 together. As a first attempt, we may assume that the basic signature $\mathcal{S}_{0}$ contains covariant type constructors pre and maybe and invariant type constructors pre $_{=}$and maybe $=$, all of kind $\star \Rightarrow \diamond$ and two type constructors abs and either of kind $\diamond$, and that the subtype ordering $\leqslant$ is defined by the following diagram:

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-133.jpg?height=285&width=436&top_left_y=939&top_left_x=948)

Intuitively, we wish that pre $=$ and maybe $=$ be logically invariant, pre and maybe be logically covariant, and the equivalences pre $=\mathrm{T} \leq$ maybe $_{=} \mathrm{T}^{\prime} \equiv \mathrm{T}=\mathrm{T}^{\prime}$ and

$$
\begin{equation*}
\text { pre }=\mathrm{T} \leq \text { pre } \mathrm{T}^{\prime} \equiv \text { pre } \mathrm{T} \leq \text { maybe } \mathrm{T}^{\prime} \equiv \text { maybe }_{=} \mathrm{T} \leq \text { maybe } \mathrm{T}^{\prime} \equiv \mathrm{T} \leq \mathrm{T}^{\prime} \tag{1}
\end{equation*}
$$

simultaneously hold. However, (1) requires, for instance, type constructors pre $=$ and pre to have the same direction, which is not currently possible since they do not have the same variance. Interestingly, this restriction may be relaxed by assigning variances of directions on a per type constructor basis and define structural subtyping accordingly (See Exercise 1.11.30). Then, replacing all occurrences of pre by pre $=$ in $\Gamma_{0}$ preserves type soundness and allows for both accurate record types and flexible subtyping in the same setting.

1.11.30 ExERcise [RELaXed variances, $\star \star \star, \nrightarrow]$ : Let $\emptyset$ be allowed as a new variance, let extend the composition of variances defined in Example 1.3.9 with $\nu \emptyset=\emptyset$, and let $\leqslant \emptyset$ stands for the full relation on type constructors. Let each type constructor $F$ of signature $K \Rightarrow \kappa$ now come with a mapping $\vartheta(F)$ from $\operatorname{dom}(K)$ to variances. Let $\vartheta\left(t, t^{\prime}, \pi\right)$ be the variance of two
ground types $t$ and $t^{\prime}$ at a path $\pi$ recursively defined by $\vartheta\left(t, t^{\prime}, d \cdot \pi\right)=$ $\left(\vartheta(t(\epsilon))(d) \cap \vartheta\left(t^{\prime}(\epsilon)\right)(d)\right) \vartheta\left(t / d, t^{\prime} / d, \pi\right)$ and $\vartheta\left(t, t^{\prime}, \epsilon\right)=+$. Then define the interpretation of subtyping as follows: if $t, t^{\prime} \in \mathcal{M}_{\kappa}$, let $t \leq t^{\prime}$ hold if and only if for all path $\pi \in \operatorname{dom}(t) \cap \operatorname{dom}\left(t^{\prime}\right), t(\pi) \leqslant^{\vartheta\left(t, t^{\prime}, \pi\right)} t^{\prime}(\pi)$ holds.

Check that the relation $\leq$ remains a partial ordering. Check that a type constructor whose direction $d$ has been syntactically declared covariant (respectively contravariant, invariant) is still logically covariant (respectively contravariant, invariant) in $d$.

\section*{Record concatenation}

Record concatenation takes two records and combines them into a new record whose fields are taken from whatever argument defines them. Of course, there is an ambiguity when the two records do not have disjoint domains and a choice should be made to disambiguate such cases. Symmetric concatenation let concatenation be undefined in this case (Harper and Pierce, 1991), while asymmetric concatenation let one-side (usually the right side) always take priority. Despite a rather simple semantics, record concatenation remains hard to type (with either a strict or a priority semantics). Solutions to type inference for record concatenation may be found, for instance, in (Wand, 1989; Rémy, 1992; Pottier, 2000).

\section*{Polymorphic variants}

Variants can be defined via algebraic data-type definitions. However, as fields for records, variant tags are taken from a relatively small, finite collection of labels and two variant definitions will have incompatible types. Thus, to remain compatible, two variants must chose their tag among a larger collection that is a superset of all the possible tags of either variant. In general, this reduces the accuracy of types and forces useless dynamic checks for tags that could otherwise be known not to occur. Extensible variants (page 93) allow to work with an arbitrary large collection of tags, but do not improve accuracy. Polymorphic variants refers to a more precise typechecking mechanism for variants, where types more accurately describes the tags that may actually occur. They allow to build values of sum types out of a large, potentially infinite predefined set of tags and call polymorphic functions to explore them. As for record, this problem could be tackled by first considering polymorphic operations over variants built from a finite set of tags and total variants with an infinite set of tag independently and then by combining both approaches together. We propose a direct solution by a simple analogy with records.

Indeed, type constructor pre can be used to distinguish a (finite) set of tags
that the variant may actually carry, from other tags that are certain not to occur and typed with abs. For example, a variant $\ell$.v, built from a value $\mathrm{v}$ with a constructor tag $\ell$ of arity one. may be assigned the principal type scheme $\forall \mathrm{X} . \Sigma(\ell:$ pre $\mathrm{T} ; \mathrm{X})$ where $\mathrm{T}$ is the type of $\mathrm{v}$. The unary type constructor $\Sigma$ is used to coerce rows to variant types-thus, variant types and record types may share the same inner row structure and be simply distinguished by their top symbol. An instance of this polymorphic type is $\forall \mathrm{X} . \Sigma(\ell$ :pre $\mathrm{T}$; abs $)$, which tells that the variant must have been built with tag $\ell$ and no other tag, thus retaining exact information about the shape of the value. Another instance of the variant polymorphic type is $\Sigma\left(\ell:\right.$ pre $\mathrm{T} ; \ell^{\prime}:$ pre $\mathrm{T}^{\prime}$; abs $)$. Indeed, it is sound to assume that the value might also have been built with some other $\operatorname{tag} \ell^{\prime}$, even if we know that this is not actually the case. Interestingly, both values $\ell$.v and $\ell^{\prime}$.v have this type and can be mixed at this type.

We use filters to explore variants. A filter $\left[\ell: \mathrm{v} \mid \mathrm{v}^{\prime}\right]$ is a function that expects a variant argument, thus of the form $\ell^{\prime}$.w. It then proceeds with either $\mathrm{v} \mathrm{w}$, if $\ell^{\prime}=\ell$, or $\mathrm{v}^{\prime} \mathrm{w}$ otherwise. The type of this filter is $\Sigma\left(\ell:\right.$ pre $\left.\mathrm{T} ; \mathrm{T}^{\prime}\right) \rightarrow \mathrm{T}^{\prime \prime}$ where $\mathrm{T}$ is the type of values accepted by $\mathrm{v}, \Sigma\left(\ell: \mathrm{T}^{\prime \prime \prime} ; \mathrm{T}^{\prime}\right)$ is the type of values accepted by $\mathrm{v}^{\prime}$, and $\mathrm{T}^{\prime \prime}$ is the type of values returned by both $\mathrm{v}$ and $\mathrm{v}^{\prime}$. Any type $\mathrm{T}^{\prime \prime \prime}$ would do, including, in particular, abs. Indeed, when w is passed to $\mathrm{v}^{\prime}$, it is known not to have tag $\ell$, so the behavior of $\mathrm{v}^{\prime}$ on $\ell$ does not matter. The null filter [] can be used for $\mathrm{v}^{\prime}$. This filter should actually never be applied, which we ensure by assigning $\square$ the type $\forall \mathrm{X} . \Sigma(\partial \mathrm{abs}) \rightarrow \mathrm{X}$, for no variant value has type $\Sigma(\partial \mathrm{abs})$. For instance, the filter $\left[\ell: \mathrm{v}_{\ell} \mid\left[\ell^{\prime}: \mathrm{v}_{\ell^{\prime}} \mid[]\right]\right]$, which may be abbreviated as $\left[\ell: \mathrm{v}_{\ell} \mid \ell^{\prime}: \mathrm{v}_{\ell^{\prime}}\right]$ can be applied to either $\ell$.v or $\ell^{\prime} . \mathrm{v}^{\prime}$. The following example formalizes polymorphic variants.

1.11.31 Example [Polymorphic variants]: Let $\star$ and $\diamond$ be two basic kinds. Let $\mathcal{S}$ contain in addition to the arrow type constructor the two type constructors pre of kind $\star \Rightarrow \diamond$ and abs of kind $\diamond$. In the presence of subtyping we may assume abs $\leqslant$ pre. Let $\mathcal{S}_{1}$ contain the unique covariant isolated type constructor $\Sigma$ of kind $\diamond \Rightarrow \star$. Let $\Gamma_{0}$ be composed of unary constructors $(\ell . \cdot)^{\ell \in \mathcal{L}}$ and primitives [ of arity 0 and $([\ell: \cdot \mid \cdot] \cdot)^{\ell \in \mathcal{L}}$ of arity 3 , given with the following reduction rules:

$$
\begin{aligned}
& {\left[\ell: \mathrm{v} \mid \mathrm{v}^{\prime}\right] \ell . \mathrm{w} \quad \xrightarrow{\delta} \quad \mathrm{v} \mathrm{w}} \\
& {\left[\ell: \mathrm{v} \mid \mathrm{v}^{\prime}\right] \ell^{\prime} . \mathrm{w} \quad \xrightarrow{\delta} \quad \mathrm{v}^{\prime} \mathrm{w} \quad \text { if } \ell \neq \ell^{\prime}}
\end{aligned}
$$

and contain the following typing assumptions:

$$
\begin{aligned}
\ell . \cdot: & \forall \mathrm{XY} . \mathrm{X} \rightarrow \Sigma(\ell: \text { pre } \mathrm{X} ; \mathrm{Y}) \\
{[]: } & \forall \mathrm{X} . \Sigma(\partial \mathrm{abs}) \rightarrow \mathrm{X} \\
{[\ell: \cdot \mid \cdot]: } & \forall \mathrm{XX}^{\prime} \mathrm{YY} \mathrm{Y}^{\prime} .(\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow\left(\Sigma\left(\ell: \mathrm{X}^{\prime} ; \mathrm{Y}^{\prime}\right) \rightarrow \mathrm{Y}\right) \rightarrow \Sigma\left(\ell: \operatorname{pre} \mathrm{X} ; \mathrm{Y}^{\prime}\right) \rightarrow \mathrm{Y}
\end{aligned}
$$

1.11.32 ExERcise [Soundness for Extensible Variants, $\star \star \star \star, \nrightarrow$ ]: Prove type soundness for extensible variants in both equality-only and subtyping models.

\section*{Other applications of rows}

Polymorphic records and variants are the most well-known applications of rows. Besides the many variations on their presentations - we have only illustrated some of them-there are several other interesting applications of rows.

Since objects can be viewed as record-of-functions, at least from a typing point of view, rows can also be used to type structural objects (Wand, 1994; Rémy, 1994; Rémy and Vouillon, 1998) and provide, in particular, polymorphic method invocation. This is the key to typechecking objects in Objective Caml (Rémy and Vouillon, 1998). First-class messages (Nishimura, 1998; Müller and Nishimura, 1998; Pottier, 2000) combine records and variants in an interesting way: while filters over variant types enforce all branches to have the same return type, first-class messages treat filters as records of functions (also called objects) rather than functions from a variant type to a shared return type. A message is an element of a variant type. The application of an object to a message, that is of a record of functions to a variant type, selects from the record the branch labeled with the same tag as the message and applies it to the content of the message, much as pattern matching. However, these applications are typechecked more accurately by first restricting the domain of the record to the set of tags that the message may possibly carry, and thus other branches and in particular their return type are left unconstrained.

Row types may also represent set of properties within types or type refinements and be used in type systems for program analysis. Two examples worth mentioning are their application to soft-typing (Cartwright and Fagan, 1991; Wright and Cartwright, 1994) and typechecking of uncaught exceptions (Leroy and Pessaux, 2000).

The key to rows is to decompose the set of row labels into a class of finite partitions that is closed by some operations. Here, those partitions are composed of singleton labels and co-finite sets of labels; the operations are merging (or conversely splitting) a singleton label and a co-finite set of labels. Other decompositions are possible, for instance, one could imagine to consider labels in a two-dimensional space. More generally, labels might also be given internal structure, for instance, one might consider automatons as labels. Notice also that record types are stratified, since rows, that is, expressions of kind $\operatorname{Row}(L)$, may not themselves contain records - constructors of $\mathcal{S}_{1}$ are only given the image row kind Type. This restriction can be partially
relaxed leading to rows of increasing degrees (Rémy, 1992b) ... and complexity! Yet more intriguing are typed-indexed rows where labels are themselves types (Shields and Meijer, 2001).

\section*{Alternatives to rows}

The original idea of using rows to describe types of extensible records is due to Wand (Wand, 1987, 1988). A key simplification to row types is to make them total functions from labels to types and encode definiteness explicitly in the structure of fields, for instance with pre and abs type constructors, as presented here. This decomposition reduces the resolution of unification constraints to a simple equational reasoning (Rémy, 1993, 1992a). Other approaches that do not treat rows as total functions seem more $a d$ hoc and have often hard-wired restrictions (Jategaonkar and Mitchell, 1988; Ohori and Buneman, 1989; Berthomieu, 1993; Ohori, 1999). Among these partial solutions, (Ohori, 1999) is quite interesting for its overall simplicity in the case where polymorphic access alone is required. Rows and fields may also be represented within ad-hoc type constraints rather than terms and equality (or subtyping) constraints. For example, qualified types use the predicates ( $\mathrm{T}$ has $\ell: \mathrm{T}^{\prime}$ ) and ( $\mathrm{T}$ lacks $\ell$ ) to mean that field $\ell$ of row $\mathrm{T}$ is defined with type $\mathrm{T}^{\prime}$ or undefined, respectively (Jones, 1994b; Odersky, Sulzmann, and Wehr, 1999b). These constraints are in fact equivalent in our equality-model to $\exists \mathrm{X} . \mathrm{T}=\left(\ell\right.$ :pre $\left.\mathrm{T}^{\prime} ; \mathrm{X}\right)$ and $\exists \mathrm{X} . \mathrm{T}=(\ell:$ abs $; \mathrm{X})$, respectively. Record typechecking has also been widely studied in the presence of subtyping. Usually, record subtyping is given meaning directly and not via rows. While these solutions are quite expressive, thanks to subtyping, they still suffer from their nonstructural treatment of record types and cannot type row extension. Thus, even in subtyping models the use of rows increases expressiveness, and is usually a simplification as well. The subtyping model can then also take advantage of the possibility of enriching type constructors pre and abs with more structure and relate them via subtyping (Pottier, 2000). Notice, that even though rows have been introduced for type inference, they seem to be beneficial to explicitly typed languages as well since even other advanced solutions (Cardelli and Mitchell, 1991; Cardelli, 1992) are limited.

Rules of Figure 1-19 are one way of solving row type constraints. In a model with subtyping constraints, a more direct closure-based resolution may be more appropriate (Pottier, 2003).

B Solutions to Selected Exercises

1.2.6 Solution: The definition does not behave as expected, because if is a destructor, whose arguments-according to the call-by-value semantics of MLthe-calculus-are evaluated before R-TRUE or R-FALSE is allowed to fire. As a result, the semantics of the expression if $t_{0}$ then $t_{1}$ else $t_{2}$ is to evaluate both $t_{1}$ and $t_{2}$ before choosing one of them. Since these expressions may have side effects (for instance, they may fail to terminate, or update a reference), this semantics is undesirable. The desired evaluation order can be obtained by placing $t_{1}$ and $t_{2}$ within closures, which delays their evaluation, then invoking the closure returned by the conditional, forcing its body to be evaluated. In other words, the expression if $t_{0}$ then $t_{1}$ else $t_{2}$ should now be viewed as syntactic sugar for if $t_{0}\left(\lambda\right.$ z.t $\left._{1}\right)\left(\lambda z . t_{2}\right) \hat{0}$. The choice of the constant $\hat{0}$ is arbitrary, since it is discarded; any value would do.

1.2.21 Solution: Within Damas and Milner's type system, we have:

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-140.jpg?height=193&width=905&top_left_y=827&top_left_x=688)

Please note that, because $\mathrm{X}$ occurs free within the environment $\mathrm{z}_{1}: \mathrm{X}$, it is impossible to apply DM-GEN to the judgement $z_{1}: X \vdash z_{1}: X$ in a nontrivial way. For this reason, $z_{2}$ cannot receive the type scheme $\forall x$.X, and the whole expression cannot receive type $\mathrm{X} \rightarrow \mathrm{Y}$, where $\mathrm{X}$ and $\mathrm{Y}$ are distinct.

1.2.22 Solution: It is straightforward to prove that the identity function has type int $\rightarrow$ int:

$$
\frac{\overline{\Gamma_{0} ; z: \text { int } \vdash \mathrm{z}: \text { int }}}{\Gamma_{0} \vdash \lambda \mathrm{z} . \mathrm{z}: \text { int } \rightarrow \text { int }} \text { DM-ABS }
$$

In fact, nothing in this type derivation depends on the choice of int as the type of $z$. Thus, we may just as well use a type variable $X$ instead. Furthermore, after forming the arrow type $\mathrm{X} \rightarrow \mathrm{X}$, we may employ DM-GEN to quantify universally over $\mathrm{X}$, since it no longer appears in the environment.

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-140.jpg?height=191&width=824&top_left_y=1708&top_left_x=728)

It is worth noting that, although the type derivation employs an arbitrary type variable $\mathrm{X}$, the final typing judgement has no free type variables. It is
thus independent of the choice of $\mathrm{x}$. In the following, we refer to the above type derivation as $\Delta_{0}$.

Next, we prove that the successor function has type int $\rightarrow$ int under the initial environment $\Gamma_{0}$. We write $\Gamma_{1}$ for $\Gamma_{0} ; z$ : int, and make uses of DM-VAR implicit.

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-141.jpg?height=252&width=956&top_left_y=466&top_left_x=680)

In the following, we refer to the above type derivation as $\Delta_{1}$. We may now build a derivation for the third typing judgement. We write $\Gamma_{2}$ for $\Gamma_{0} ; f$ : int $\rightarrow$ int.

$$
\frac{\Delta_{1} \frac{\Gamma_{2} \vdash \mathrm{f}: \text { int } \rightarrow \text { int } \quad \Gamma_{2} \vdash \hat{2}: \text { int }}{\Gamma_{2} \vdash \mathrm{f} \hat{2}: \text { int }}}{\Gamma_{0} \vdash \text { let } \mathrm{f}=\lambda \mathrm{z} \cdot \mathrm{z} \hat{+} \hat{1} \text { in } \mathrm{f} \hat{2}: \text { int }} \text { DM-LET }
$$

To derive the fourth typing judgement, we re-use $\Delta_{0}$, which proves that the identity function has polymorphic type. We write $\Gamma_{3}$ for $\Gamma_{0} ; f: \forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$. By DM-VAR and DM-INST, we have $\Gamma_{3} \vdash \mathrm{f}:($ int $\rightarrow$ int $) \rightarrow($ int $\rightarrow$ int) and $\Gamma_{3} \vdash f:$ int $\rightarrow$ int. Thus, we may build the following derivation:

$$
\begin{aligned}
& \Gamma_{3} \vdash \mathrm{f}:(\text { int } \rightarrow \text { int }) \rightarrow(\text { int } \rightarrow \text { int })
\end{aligned}
$$

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-141.jpg?height=256&width=846&top_left_y=1290&top_left_x=806)

The first and third judgements are valid in the simply-typed $\lambda$-calculus, because they use neither DM-GEN nor DM-INST, and use DM-LET only to introduce the monomorphic binding $\mathrm{f}:$ int $\rightarrow$ int into the environment. The second judgement, of course, is not: because it involves a nontrivial type scheme, it is not even a well-formed judgement in the simply-typed $\lambda$-calculus. The fourth judgement is well-formed, but not derivable, in the simply-typed $\lambda$-calculus. This is because $f$ is used at two incompatible types, namely (int $\rightarrow$ int) $\rightarrow$ (int $\rightarrow$ int) and int $\rightarrow$ int, inside the expression $\mathrm{f} f \hat{2}$. Both of these types are instances of $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$, the type scheme assigned to $f$ in the environment $\Gamma_{3}$.

By inspection of DM-VAR, DM-GEN, and DM-INST, it is straightforward to see that, if $\Gamma_{0} \vdash \hat{1}: \mathrm{T}$ is derivable, then $\mathrm{T}$ must be int. Since int is not an arrow type, the application $\hat{1} \hat{2}$ cannot be well-typed under $\Gamma_{0}$. In fact, because this expression is stuck, it cannot be well-typed in a sound type system.

The expression $\lambda f$. $(f f)$ is ill-typed in the simply-typed $\lambda$-calculus, because no type $\mathrm{T}$ may coincide with a type of the form $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$. Indeed, $\mathrm{T}$ would then be a subterm of itself. For the same reason, this expression is ill-typed in $\mathrm{DM}$ as well. Indeed, it is not difficult to check that the presence of DM-GEN and DM-INST makes no difference: DM-GEN cannot generalize $\mathrm{T}$ as long as the binding $f: T$ appears in the environment, and DM-INST can only instantiate $T$ to $T$ itself. Thus, the self-application $f f$ is well-typed in DM only if $f$ is let-bound, as opposed to $\lambda$-bound. The argument crucially relies on the fact that $f$ must be assigned a monotype. Indeed, the expression $\lambda f .(f f)$ is well-typed in an implicitly-typed variant of System F: one of its types is $(\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}) \rightarrow(\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X})$. It also relies on the fact that types are finite: indeed, this expression is well-typed in an extension of the simply-typed $\lambda$ calculus with recursive types, where the equation $\mathrm{T}=\mathrm{T} \rightarrow \mathrm{T}^{\prime}$ has a solution.

1.2.23 Solution: It is clear that the effect of DM-GEN may be obtained by a series of successive applications of DM-GEN'. Conversely, consider an instance of DM-GEN', whose premises are $\Gamma \vdash \mathrm{t}: \mathrm{S}(\mathbf{1})$ and $\mathrm{X} \notin f t v(\Gamma)$ (2). Let us write $\mathrm{S}=\forall \overline{\mathrm{X}} . \mathrm{T}$, where $\overline{\mathrm{X}} \# f t v(\Gamma)$ (3). Applying DM-Inst to (1) and to the identity substitution yields $\Gamma \vdash \mathrm{t}: \mathrm{T}$ (4). Applying DM-GEN to (4), (2) and (3) yields $\Gamma \vdash t: \forall x \bar{x} . T$, that is, $\Gamma \vdash t: \forall X$.S. Thus, the effect of DM-GEN' may be obtained by DM-INST and DM-GEN.

It is clear that DM-INST is a particular case of DM-INST' where $\bar{Y}$ is empty. Conversely, consider an instance of DM-INST', whose premises are $\Gamma \vdash t$ : $\forall \overline{\mathrm{X}}$.T (1) and $\overline{\mathrm{Y}} \# \operatorname{ftv}(\forall \overline{\mathrm{X}}$. T) (2). Let $\rho$ be a renaming that exchanges $\overline{\mathrm{Y}}$ with $\overline{\mathrm{Z}}$, where $\overline{\mathrm{Z}} \# \operatorname{ftv}(\forall \overline{\mathrm{Y}} .[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T})$ (3) and $\overline{\mathrm{Z}} \# \operatorname{ftv}(\Gamma)$ (4). Applying DM-InsT to (1) yields $\Gamma \vdash \mathrm{t}:[\overrightarrow{\mathrm{X}} \mapsto \rho \overrightarrow{\mathrm{T}}] \mathrm{T}$ (5). Applying DM-GEN to (5) and (4) yields $\Gamma \vdash$ $\mathrm{t}: \forall \overline{\mathrm{Z}} \cdot[\overrightarrow{\mathrm{X}} \mapsto \rho \overrightarrow{\mathrm{T}}] \mathrm{T}$, that is, $\Gamma \vdash \mathrm{t}: \forall \rho \overline{\mathrm{Y}} .[\overrightarrow{\mathrm{X}} \mapsto \rho \overrightarrow{\mathrm{T}}] \mathrm{T}$ (6). Now, by (2) and (3), we have $[\overrightarrow{\mathrm{X}} \mapsto \rho \overrightarrow{\mathrm{T}}] \mathrm{T}=\rho([\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T})$, so (6) may be written $\Gamma \vdash \mathrm{t}: \forall \rho \overline{\mathrm{Y}} . \rho([\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T})$, that is, $\Gamma \vdash \mathrm{t}: \rho(\forall \overline{\mathrm{Y}} .[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T})(7)$. By (3), this is exactly $\Gamma \vdash \mathrm{t}: \forall \overrightarrow{\mathrm{Y}} \cdot[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$. Thus, the effect of DM-INST' may be obtained by DM-INST and DM-GEN.

1.4.4 Solution: Let us recall that a program $t$ is well-typed if and only if a judgement of the form $C, \Gamma \vdash \mathrm{t}: \sigma$, where $C$ is satisfiable, holds. Let us show that it is in fact possible, without loss of generality, to require $\sigma$ to be a monotype.

Assume $C, \Gamma \vdash \mathrm{t}: \sigma(\mathbf{1})$ is derivable within $\operatorname{HM}(X)$. Let us write $\sigma=$ $\forall \overline{\mathrm{X}}[D]$.T, where $\overline{\mathrm{X}} \# f t v(C)$ (2). Applying Lemma 1.4.1 to (1) yields $C \Vdash$ $\exists \overline{\mathrm{X}} . D$ (3). By hm-Inst, (1) implies $C \wedge D, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (4). By (3), we have $C \equiv C \wedge \exists \overline{\mathrm{x}} . D \equiv \exists \overline{\mathrm{X}} .(C \wedge D)$. Because $C$ is satisfiable, this implies that $C \wedge D$
is satisfiable as well. Thus, the judgement (4), which involves the monotype $\mathrm{T}$, witnesses that $\mathrm{t}$ is well-typed.

We have shown that a program $t$ is well-typed if and only if a judgement of the form $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$, where $C$ is satisfiable, holds. Thus, by Theorems ?? and ??, well-typedness is the same for both rule sets.

1.4.5 Solution: By Theorem ??, every rule in Figure 1-8 is admissible in $\operatorname{HM}(X)$. Of course, so is HM-GEN. So, every judgement that is derivable via the rules of Figure 1-8 and $\mathrm{HM}-\mathrm{GEN}$ is a valid $\operatorname{HM}(X)$ judgement.

Conversely, assume $C, \Gamma \vdash \mathrm{t}: \sigma$ (1) holds in $\operatorname{HM}(X)$. We must show that it is derivable via the rules of Figure 1-8 and HM-GEN. Let us write $\sigma=$ $\forall \overline{\mathrm{x}}[D]$.T, where $\overline{\mathrm{x}} \# \mathrm{ftv}(C, \Gamma)$ (2). By HM-Inst and (1), the judgement $C \wedge$ $D, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (3) holds in $\operatorname{HM}(X)$. This judgement involves a monotype, so, by Theorem ??, it is derivable via the rules of Figure 1-8. Furthermore, from (3) and (2), HM-GEN allows deriving $C \wedge \exists \sigma, \Gamma \vdash \mathrm{t}: \sigma$ (4). Applying Lemma 1.4.1 to (1) yields $C \Vdash \exists \sigma$, so the judgement (4) may be written $C, \Gamma \vdash \mathrm{t}: \sigma$. We have shown that (1) is derivable via the rules of Figure 1-8 and HM-GEN. In fact, it is possible to apply HM-GEN only once, at the end of the derivation.

1.5.1 Solution: Within the type system $\operatorname{PCB}(X)$, we have

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-143.jpg?height=191&width=1114&top_left_y=1124&top_left_x=601)

The type variable $z$, which occurs free in the left-hand instance of VAR, is generalized. However, $\mathrm{z}_{2}$ does not receive the type scheme $\forall \mathrm{Z} . \mathrm{Z}$, which, as suggested earlier, is unsound; instead, it receives the constrained type scheme $\forall z\left[z_{1} \preceq z\right] . z$. The latter is more restrictive than the former: indeed, the former claims that $z_{2}$ has every type, while the latter only claims that every valid type for $z_{1}$ is also a valid type for $z_{2}$. Let us now examine the constraint let $z_{1}$ : $\mathrm{X} ; \mathrm{z}_{2}: \forall \mathrm{Z}\left[\mathrm{z}_{1} \preceq \mathrm{Z}\right] . \mathrm{Z}$ in $\mathrm{z}_{2} \preceq \mathrm{Y}$, which appears at the root of the derivation. By C-INID and C-IN*, it is equivalent to let $\mathrm{z}_{1}: \mathrm{X}$ in $\exists \mathrm{Z} .\left(\mathrm{z}_{1} \preceq \mathrm{Z} \wedge \mathrm{Z} \leq \mathrm{Y}\right)$ and to $\exists \mathrm{Z}$. $\mathrm{X} \leq \mathrm{Z} \wedge \mathrm{Z} \leq \mathrm{Y}$ ), which by $\mathrm{C}$-ExTRans is equivalent to $\mathrm{X} \leq \mathrm{Y}$. Thus, the judgement at the root of the above derivation may be written $\mathrm{X} \leq$ $\mathrm{Y} \vdash \lambda \mathrm{z}_{1}$. let $\mathrm{z}_{2}=\mathrm{z}_{1}$ in $\mathrm{z}_{2}: \mathrm{X} \rightarrow \mathrm{Y}$. In other words, the expression let $\mathrm{z}_{2}=$ $\mathrm{z}_{1}$ in $\mathrm{z}_{2}$ has type $\mathrm{X} \rightarrow \mathrm{Y}$ only under the assumption that $\mathrm{X}$ is a subtype of $\mathrm{Y}$, which is sound. Even though LET allows unrestricted generalization of type variables, it remains sound, because the type scheme that it produces typically has free program identifiers, such as $\forall \mathrm{Z}\left[\mathbf{z}_{1} \preceq \mathrm{Z}\right] . \mathrm{Z}$ above.

1.7.10 Solution: Let $\mathcal{E}=$ let $\mathrm{z}=\mathcal{E}_{1}$ in $\mathrm{t}_{1}$ and $\mathcal{E}_{1}[\mathrm{t}] / \mu \sqsubseteq \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}$ (1). Then,

$$
\begin{align*}
& \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket \mathcal{E}[\mathrm{t}] / \mu: \mathrm{T} / M \rrbracket \\
= & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in }\left(\left(\text { let } \mathrm{z}: \forall \mathrm{x}\left[\llbracket \mathcal{E}_{1}[\mathrm{t}]: \mathrm{x} \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket\right) \wedge \llbracket \mu: M \rrbracket\right)  \tag{2}\\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M ; \mathrm{z}: \forall \mathrm{x}\left[\llbracket \mathcal{E}_{1}[\mathrm{t}] / \mu: \mathrm{X} / M \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket  \tag{3}\\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M ; \mathrm{z}: \forall \mathrm{x}\left[\text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket \mathcal{E}_{1}[\mathrm{t}] / \mu: \mathrm{x} / M \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket  \tag{4}\\
\Vdash & \text { let } \Gamma_{0} ; \operatorname{ref} M ; \mathrm{z}: \forall \mathrm{x} \overline{\mathrm{Y}}\left[\text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}: \mathrm{x} / M^{\prime} \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket \tag{5}
\end{align*}
$$

where (2) is by definition of constraint generation, where $\mathrm{X} \notin \operatorname{ftv}(\mathrm{T}, M)(\mathbf{6}) ;(3)$ is by (6), C-LETAND, and by definition of constraint generation; (4) is by (6) and C-LetDup; (5) follows from (1) and C-LETEx, for some $\overline{\mathrm{Y}}$ and $M^{\prime}$ such that $\overline{\mathrm{Y}} \# \operatorname{ftv}(\mathrm{X}, M)(\mathbf{7})$ and $f t v\left(M^{\prime}\right) \subseteq \overline{\mathrm{Y}} \cup f t v(M)$ (8) and $\operatorname{dom}\left(M^{\prime}\right)=\operatorname{dom}\left(\mu^{\prime}\right)$ and $M^{\prime}$ extends $M$. Note that (6), (7) and (8) imply $\mathrm{X} \notin f t v\left(M^{\prime}\right)$ (9).

At this point, the type variables $\overline{\mathrm{Y}}$, which determine the types of the newly allocated store cells, are universally quantified in the type scheme assigned to $z$, which is undesirable. We are stuck, because we cannot in general apply C-LETALL to hoist $\exists \bar{Y}$ out of the let constraint. Let us now assume that, by some external means, we are guaranteed $\overline{\mathrm{Y}}=\varnothing \mathbf{( 1 0 )}$. Then, we may proceed as follows:

$$
\begin{align*}
& \equiv \text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} ; \mathrm{z}: \forall \mathrm{X}\left[\text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}: \mathrm{X} / M^{\prime} \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket  \tag{11}\\
& \equiv \text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket \mathcal{E}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket \tag{12}
\end{align*}
$$

where (11) follows from the fact the the memory locations that appear free in $\llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket$ are members of $\operatorname{dom}(\mu)$, thus are not members of $\operatorname{dom}\left(M^{\prime}\right) \backslash \operatorname{dom}(M)$; (12) is obtained by performing the steps that lead to (4) in reverse.

The requirement that $\overline{\mathrm{Y}}$ be empty, that is, $f t v(M)=f t v\left(M^{\prime}\right)$, is classic (Tofte, 1988). How is it enforced? Assume that the left-hand side of every let construct is required to be a non-expansive expression. By assumptions (ii) and (iii), this invariant is preserved by reduction. So, $\mathcal{E}_{1}[t]$ must be nonexpansive, which, by assumption (i), guarantees that the reduction step does not allocate new memory cells. Then, $\mu^{\prime}$ is $\mu$, so $M^{\prime}$ is $M$.

1.9.1 Solution: We must first ensure that R-AdD respects $\sqsubseteq$ (Definition 1.7.5). Since the rule is pure, it is sufficient to establish that let $\Gamma_{0}$ in $\llbracket \hat{k}_{1} \hat{+} \hat{k}_{2}: \mathrm{T} \rrbracket$ entails let $\Gamma_{0}$ in $\llbracket \widehat{k_{1}+k_{2}}: \mathrm{T} \rrbracket$. In fact, we have

$$
\begin{align*}
& \text { let } \Gamma_{0} \text { in } \llbracket \hat{k}_{1} \hat{+} \hat{k}_{2}: \mathrm{T} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XY} .\left(\hat{+} \preceq \mathrm{X} \rightarrow \mathrm{Y} \rightarrow \mathrm{T} \wedge \hat{k}_{1} \preceq \mathrm{X} \wedge \hat{k}_{2} \preceq \mathrm{Y}\right)  \tag{1}\\
\equiv & \exists \mathrm{XY} .(\text { int } \rightarrow \text { int } \rightarrow \text { int } \leq \mathrm{X} \rightarrow \mathrm{Y} \rightarrow \mathrm{T} \wedge \text { int } \leq \mathrm{X} \wedge \text { int } \leq \mathrm{Y})  \tag{2}\\
\equiv & \exists \mathrm{XY} .(\mathrm{X}=\operatorname{int} \wedge \mathrm{Y}=\operatorname{int} \wedge \text { int } \leq \mathrm{T})  \tag{3}\\
\equiv & \text { int } \leq \mathrm{T}  \tag{4}\\
\equiv & \text { let } \Gamma_{0} \text { in } \llbracket \widehat{k_{1}+k_{2}}: \mathrm{T} \rrbracket \tag{5}
\end{align*}
$$
where (1) is by definition of constraint generation; (2) is by definition of $\Gamma_{0}$, by C-INID and C-IN*; (3) is by C-ARRow and by antisymmetry of subtyping;

(4) is by C-ExAnd and C-NAmE; (5) is again by definition of $\Gamma_{0}$, by C-InId and $\mathrm{C}-\mathrm{IN}^{*}$, and by definition of constraint generation.

Second, we must check that if the configuration $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$ (where $k \geq 0$ ) is well-typed, then either it is reducible, or $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k}$ is a value.

We begin by checking that every value that is well-typed with type int is of the form $\hat{k}$. Indeed, suppose that let $\Gamma_{0} ; \operatorname{ref} M$ in $\llbracket \mathrm{v}:$ int $\rrbracket$ is satisfiable. Then, $v$ cannot be a program variable, for a well-typed value must be closed. v cannot be a memory location $m$, for otherwise ref $M(m) \leq$ int would be satisfiable - but the type constructors ref and int are incompatible. $v$ cannot be $\hat{+}$ or $\hat{+} \mathrm{v}^{\prime}$, for otherwise int $\rightarrow$ int $\rightarrow$ int $\leq$ int or int $\rightarrow$ int $\leq$ int would be satisfiable - but the type constructors $\rightarrow$ and int are incompatible. Similarly, $\mathrm{v}$ cannot be a $\lambda$-abstraction. Thus, $\mathrm{v}$ must be of the form $\hat{k}$, for it is the only case left.

Next, we note that, according to the constraint generation rules, if the configuration $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$ is well-typed, then a constraint of the form let $\Gamma_{0}$; ref $M$ in $\left(\mathrm{c} \preceq \mathrm{x}_{1} \rightarrow \ldots \rightarrow \mathrm{x}_{k} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}_{1}: \mathrm{x}_{1} \rrbracket \wedge \ldots \wedge \llbracket \mathrm{v}_{k}: \mathrm{x}_{k} \rrbracket\right)$ is satisfiable. We now reason by cases on $c$.
- Case $\mathrm{c}$ is $\hat{k}$. Then, $\Gamma_{0}(\mathrm{c})$ is int. Because the type constructors int and $\rightarrow$ are incompatible with each other, this implies $k=0$. Since $\hat{k}$ is a constructor, the expression is a value.
- Case $\mathrm{c}$ is $\hat{+}$. We may assume $k \geq 2$, because otherwise the expression is a value. Then, $\Gamma_{0}(\mathrm{c})$ is int $\rightarrow$ int $\rightarrow$ int, so, by C-Arrow, the above constraint entails let $\Gamma_{0} ; \operatorname{ref} M$ in $\left(\mathrm{x}_{1} \leq \operatorname{int} \wedge \mathrm{X}_{2} \leq \operatorname{int} \wedge \llbracket \mathrm{v}_{1}: \mathrm{X}_{1} \rrbracket \wedge \llbracket \mathrm{v}_{2}: \mathrm{X}_{2} \rrbracket\right)$, which, by Lemma 1.6.3, entails let $\Gamma_{0} ; \operatorname{ref} M$ in $\left(\llbracket \mathrm{v}_{1}: \operatorname{int} \rrbracket \wedge \llbracket \mathrm{v}_{2}\right.$ : int $\left.\rrbracket\right)$. Thus, $\mathrm{v}_{1}$ and $\mathrm{v}_{2}$ are well-typed with type int. By the remark above, they must be integer literals $\hat{k}_{1}$ and $\hat{k}_{2}$. As a result, the configuration is reducible by R-ADD.

1.9.5 Solution: We must first ensure that R-Ref, R-Deref and R-Assign respect $\sqsubseteq($ Definition 1.7.5).
- Case R-REF. The reduction is ref v/ $\varnothing \longrightarrow m /(m \mapsto \mathrm{v})$, where $m \notin$ fpi(v) (1). Let $\mathrm{T}$ be an arbitrary type. According to Definition 1.7.5, the goal is to show that there exist a set of type variables $\overline{\mathrm{Y}}$ and a store type $M^{\prime}$ such that $\overline{\mathrm{Y}} \# \operatorname{ftv}(\mathrm{T})$ and $f t v\left(M^{\prime}\right) \subseteq \overline{\mathrm{Y}}$ and $\operatorname{dom}\left(M^{\prime}\right)=\{m\}$ and let $\Gamma_{0}$ in $\llbracket$ ref $\mathrm{v}: \mathrm{T} \rrbracket$
entails $\exists \overline{\mathrm{Y}}$.let $\Gamma_{0}$; ref $M^{\prime}$ in $\llbracket m /(m \mapsto \mathrm{v}): \mathrm{T} / M^{\prime} \rrbracket$. Now, we have

$$
\begin{align*}
& \text { let } \Gamma_{0} \text { in } \llbracket \operatorname{ref} \mathrm{v}: \mathrm{T} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XY} .(\mathrm{Y} \rightarrow \operatorname{ref} \mathrm{Y} \leq \mathrm{X} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}: \mathrm{X} \rrbracket)  \tag{2}\\
\equiv & \exists \mathrm{Y} . \text { let } \Gamma_{0} \text { in }(\operatorname{ref} \mathrm{Y} \leq \mathrm{T} \wedge \llbracket \mathrm{v}: \mathrm{Y} \rrbracket)  \tag{3}\\
\equiv & \exists \mathrm{Y} . \text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in }\left(m \preceq \mathrm{T} \wedge \llbracket \mathrm{v}: M^{\prime}(m) \rrbracket\right)  \tag{4}\\
\equiv & \exists \mathrm{Y} . \text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket m /(m \mapsto \mathrm{v}): \mathrm{T} / M^{\prime} \rrbracket \tag{5}
\end{align*}
$$

where (2) is by definition of constraint generation and by definition of $\Gamma_{0}(\mathrm{ref})$; (3) is by C-Arrow, Lemma 1.6.4, and C-InEx; (4) assumes $M^{\prime}$ is defined as $m \mapsto \mathrm{Y}$, and follows from (1), C-INID and C-IN*; and (5) is by definition of constraint generation.

Subcase R-DEREF. The reduction is $! m /(m \mapsto \mathrm{v}) \longrightarrow \mathrm{v} /(m \mapsto \mathrm{v})$. Let $\mathrm{T}$ be an arbitrary type and let $M$ be a store type of domain $\{m\}$. We have

$$
\begin{align*}
& \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket ! m /(m \mapsto \mathrm{v}): \mathrm{T} / M \rrbracket \\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \exists \mathrm{XY} .(\operatorname{ref} \mathrm{Y} \rightarrow \mathrm{Y} \leq \mathrm{X} \rightarrow \mathrm{T} \wedge m \preceq \mathrm{X} \wedge \llbracket \mathrm{v}: M(m) \rrbracket)  \tag{1}\\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \exists \mathrm{XY} .(\operatorname{ref} M(m) \leq \mathrm{X} \leq \operatorname{ref} \mathrm{Y} \wedge \mathrm{Y} \leq \mathrm{T} \wedge \llbracket \mathrm{v}: M(m) \rrbracket)  \tag{2}\\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \exists \mathrm{Y} .(M(m)=\mathrm{Y} \wedge \mathrm{Y} \leq \mathrm{T} \wedge \llbracket \mathrm{v}: M(m) \rrbracket)  \tag{3}\\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in }(M(m) \leq \mathrm{T} \wedge \llbracket \mathrm{v}: M(m) \rrbracket)  \tag{4}\\
\Vdash & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in }(\llbracket \mathrm{v}: \mathrm{T} \rrbracket \wedge \llbracket \mathrm{v}: M(m) \rrbracket)  \tag{5}\\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket \mathrm{v} /(m \mapsto \mathrm{v}): \mathrm{T} / M \rrbracket \tag{6}
\end{align*}
$$

where (1) is by definition of constraint generation and by definition of $\Gamma_{0}(!)$; (2) is by C-Arrow and C-InId; (3) follows from C-ExTrans and from the fact that ref is an invariant type constructor; (4) is by C-NAMEEQ; (5) is by Lemma 1.6.3 and C-DuP; and (6) is again by definition of constraint generation.

$\circ$ Case R-Assign. The reduction is $m:=\mathrm{v} /\left(m \mapsto \mathrm{v}_{0}\right) \longrightarrow \mathrm{v} /(m \mapsto \mathrm{v})$. Let $\mathrm{T}$ be an arbitrary type and let $M$ be a store type of domain $\{m\}$. We have

$$
\begin{align*}
& \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket m:=\mathrm{v} /\left(m \mapsto \mathrm{v}_{0}\right): \mathrm{T} / M \rrbracket \\
\Vdash & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket m:=\mathrm{v}: \mathrm{T} \rrbracket  \tag{1}\\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \exists \mathrm{XYZ} .(\operatorname{ref} \mathrm{Z} \rightarrow \mathrm{Z} \rightarrow \mathrm{Z} \leq \mathrm{X} \rightarrow \mathrm{Y} \rightarrow \mathrm{T} \wedge m \preceq \mathrm{X} \wedge \llbracket \mathrm{v}: \mathrm{Y} \rrbracket)  \tag{2}\\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \exists \mathrm{XYZ} .(\operatorname{ref} M(m) \leq \mathrm{X} \leq \operatorname{ref} \mathrm{Z} \wedge \mathrm{Z} \leq \mathrm{T} \wedge \llbracket \mathrm{v}: \mathrm{Y} \rrbracket \wedge \mathrm{Y} \leq \mathrm{Z})  \tag{3}\\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \exists \mathrm{Z} .(M(m)=\mathrm{Z} \wedge \mathrm{Z} \leq \mathrm{T} \wedge \llbracket \mathrm{v}: \mathrm{Z} \rrbracket)  \tag{4}\\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in }(M(m) \leq \mathrm{T} \wedge \llbracket \mathrm{v}: M(m) \rrbracket)  \tag{5}\\
\Vdash & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket \mathrm{v} /(m \mapsto \mathrm{v}): \mathrm{T} / M \rrbracket \tag{6}
\end{align*}
$$

where (1) and (2) are by definition of constraint generation; (3) is by CArrow and C-InId; (4) is by C-ExTrans, Lemma 1.6.4, and from the fact that ref is an invariant type constructor; (5) is by C-NAMEEQ; and (6) is obtained as in the previous case.

Second, we must check that if the configuration $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$ (where $k \geq 0$ ) is well-typed, then either it is reducible, or $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k}$ is a value. We only give a sketch of this proof; see the solution to Exercise 1.9.1 for details of a similar proof.

We begin by checking that every value that is well-typed with a type of the form ref $\mathrm{T}$ is a memory location. This assertion relies on the fact that the type constructor ref is isolated.

Next, we note that, according to the constraint generation rules, if the configuration $\mathrm{c}_{1} \ldots \mathrm{v}_{k} / \mu$ is well-typed, then a constraint of the form let $\Gamma_{0}$; ref $M$ in $\left(\mathrm{c} \preceq \mathrm{x}_{1} \rightarrow \ldots \rightarrow \mathrm{x}_{k} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}_{1}: \mathrm{x}_{1} \rrbracket \wedge \ldots \wedge \llbracket \mathrm{v}_{k}: \mathrm{x}_{k} \rrbracket\right)$ is satisfiable. We now reason by cases on $\mathrm{c}$.
- Case $\mathrm{c}$ is ref. If $k=0$, then the expression is a value; otherwise, it is reducible by $\mathrm{R}$-REF.
- Case c is !. We may assume $k \geq 1$, because otherwise the expression is a value. Then, by definition of $\Gamma_{0}(!)$, the above constraint entails let $\Gamma_{0} ; \operatorname{ref} M$ in $\exists \mathrm{Y}$.(ref $\left.\mathrm{Y} \rightarrow \mathrm{Y} \leq \mathrm{X}_{1} \rightarrow \ldots \rightarrow \mathrm{X}_{k} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}_{1}: \mathrm{X}_{1} \rrbracket\right)$, which, by C-Arrow, Lemma 1.6.3, and C-INEx, entails $\exists \mathrm{Y}$.let $\Gamma_{0} ; \operatorname{ref} M$ in $\llbracket \mathrm{v}_{1}: \operatorname{ref} \mathrm{Y} \rrbracket$. Thus, $\mathrm{v}_{1}$ is well-typed with a type of the form ref $\mathrm{Y}$. By the remark above, $\mathrm{v}_{1}$ must be a memory location $m$. Furthermore, because every well-typed configuration is closed, $m$ must be a member of $\operatorname{dom}(\mu)$. As a result, the configuration ref $\mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$ is reducible by R-DEREF.
- Case $\mathrm{c}$ is $:=$. We may assume $k \geq 2$, because otherwise the expression is a value. As above, we check that $v_{1}$ must be a memory location and a member of $\operatorname{dom}(\mu)$. Thus, the configuration is reducible by R-Assign.

1.9.6 Solution: We must first ensure that R-Fix respects $\sqsubseteq$ (Definition 1.7.5). Since the rule is pure, it is sufficient to establish that let $\Gamma_{0}$ in $\llbracket f i x v_{1} v_{2}: T \rrbracket$ entails let $\Gamma_{0}$ in $\llbracket \mathrm{v}_{1}\left(f i x v_{1}\right) \mathrm{v}_{2}: \mathrm{T} \rrbracket$. Let $C$ stand for the constraint fix $\preceq$ $((\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow(\mathrm{X} \rightarrow \mathrm{Y})) \rightarrow \mathrm{X} \rightarrow \mathrm{Y} \wedge \mathrm{Y} \leq \mathrm{T} \wedge \llbracket \mathrm{v}_{1}:(\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow(\mathrm{X} \rightarrow \mathrm{Y}) \rrbracket \wedge \llbracket \mathrm{v}_{2}: \mathrm{X} \rrbracket$. We have

$$
\begin{align*}
& \text { let } \Gamma_{0} \text { in } \llbracket \mathrm{fix} \mathrm{v}_{1} \mathrm{v}_{2}: \mathrm{T} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{X}_{1} \mathrm{X}_{2} .\left(\mathrm{fix} \preceq \mathrm{X}_{1} \rightarrow \mathrm{X}_{2} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}_{1}: \mathrm{X}_{1} \rrbracket \wedge \llbracket \mathrm{v}_{2}: \mathrm{X}_{2} \rrbracket\right)  \tag{1}\\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{X}_{1} \mathrm{X}_{2} \mathrm{XY} .\left(((\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow(\mathrm{X} \rightarrow \mathrm{Y})) \rightarrow \mathrm{X} \rightarrow \mathrm{Y} \leq \mathrm{X}_{1} \rightarrow \mathrm{X}_{2} \rightarrow \mathrm{T}\right. \\
& \left.\wedge \llbracket \mathrm{v}_{1}: \mathrm{X}_{1} \rrbracket \wedge \llbracket \mathrm{v}_{2}: \mathrm{X}_{2} \rrbracket\right)  \tag{2}\\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XY} .\left(\mathrm{Y} \leq \mathrm{T} \wedge \llbracket \mathrm{v}_{1}:(\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow(\mathrm{X} \rightarrow \mathrm{Y}) \rrbracket \wedge \llbracket \mathrm{v}_{2}: \mathrm{X} \rrbracket\right)  \tag{3}\\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XY} . C \tag{4}
\end{align*}
$$

where (1) is by definition of constraint generation; (2) is by definition of $\Gamma_{0}(f i x) ;(3)$ is by C-ARrow and Lemma 1.6.4;(4) is by definition of $\Gamma_{0}(f i x)$. By Theorem 1.6.2 and WEAKEn, the judgements $C \vdash \mathrm{v}_{1}:(\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow$
$(\mathrm{X} \rightarrow \mathrm{Y})$ and $C \vdash \mathrm{v}_{2}: \mathrm{X}$ hold. By Var, Weaken, App, and Sub, it follows that $C \vdash \mathrm{v}_{1}\left(f i x v_{1}\right) v_{2}: \mathrm{T}$ holds. By Theorem 1.6.6, this implies $C \Vdash \llbracket \mathrm{v}_{1}\left(f i x \mathrm{v}_{1}\right) \mathrm{v}_{2}: \mathrm{T} \rrbracket$. By congruence of entailment and by C-Ex*, (4) entails let $\Gamma_{0}$ in $\llbracket v_{1}\left(f i x v_{1}\right) v_{2}: T \rrbracket$.

Second, we must check that if the configuration $f i x v_{1} \ldots v_{k} / \mu$ (where $k \geq 0$ ) is well-typed, then either it is reducible, or $f i x v_{1} \ldots v_{k}$ is a value. This is immediate, for it is a value when $k<2$, and it is reducible by R-FIX when $k \geq 2$.

We now recall that the construct letrec $f=\lambda$ z.t $_{1}$ in $t_{2}$ provided by ML-the-programming-language may be viewed as syntactic sugar for let $\mathrm{f}=$ fix $\left(\lambda f . \lambda z . t_{1}\right)$ in $t_{2}$, and set forth to discover the constraint generation rule that arises out of such a definition. We have

$$
\begin{align*}
& \text { let } \Gamma_{0} \text { in } \llbracket \mathrm{fix}\left(\lambda \mathrm{f} . \lambda \mathrm{z} . \mathrm{t}_{1}\right): \mathrm{T} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{Z} .\left(\mathrm{fix} \preceq \mathrm{Z} \rightarrow \mathrm{T} \wedge \llbracket \lambda \mathrm{f} . \lambda \mathrm{z} \cdot \mathrm{t}_{1}: \mathrm{Z} \rrbracket\right)  \tag{1}\\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XY} .\left(\mathrm{X} \rightarrow \mathrm{Y} \leq \mathrm{T} \wedge \llbracket \lambda f \mathrm{f} . \lambda \mathrm{z} . \mathrm{t}_{1}:(\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow(\mathrm{X} \rightarrow \mathrm{Y}) \rrbracket\right)  \tag{2}\\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XY} .\left(\mathrm{X} \rightarrow \mathrm{Y} \leq \mathrm{T} \wedge \text { let } \mathrm{f}: \mathrm{X} \rightarrow \mathrm{Y} ; \mathrm{z}: \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{Y} \rrbracket\right) \tag{3}
\end{align*}
$$

where (1) is by definition of constraint generation; (2) is by definition of $\Gamma_{0}$ (fix), by C-ARrow, and by Lemma 1.6.4; and (3) follows from Lemma 1.6.5. This allows us to write

$$
\begin{aligned}
& \text { let } \Gamma_{0} \text { in } \llbracket \text { let } f=f i x\left(\lambda f . \lambda z . t_{1}\right) \text { in } t_{2}: T \rrbracket \\
& \equiv \text { let } \Gamma_{0} ; f: \forall \mathrm{z}\left[\llbracket \mathrm{fix}\left(\lambda \mathrm{f} \cdot \lambda \mathrm{z} \cdot \mathrm{t}_{1}\right): \mathrm{z} \rrbracket\right] . \mathrm{z} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket \\
& \equiv \text { let } \Gamma_{0} ; f: \forall \mathrm{Z}\left[\exists \mathrm{XY} .\left(\mathrm{X} \rightarrow \mathrm{Y} \leq \mathrm{Z} \wedge \text { let } \mathrm{f}: \mathrm{X} \rightarrow \mathrm{Y} ; \mathrm{z}: \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{Y} \rrbracket\right)\right] . \mathrm{Z} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket \\
& \equiv \text { let } \Gamma_{0} ; f: \forall \mathrm{XY}\left[\text { let } \mathrm{f}: \mathrm{X} \rightarrow \mathrm{Y} ; \mathrm{z}: \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{Y} \rrbracket\right] . \mathrm{X} \rightarrow \mathrm{Y} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket
\end{aligned}
$$

where (4) is by definition of constraint generation; (5) follows from C-LETDuP and from the previous series of equivalences; (6) is by C-LETEx, C-ExTrans and Lemma 1.3.22.

1.9.21 Solution: We have

$$
\begin{align*}
& \text { } \text { match }_{1} \text { with } z \cdot \mathrm{t}_{2}: \mathrm{T} \rrbracket \\
\equiv & \text { let } \forall \mathrm{xX^{ \prime }}\left[\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket \wedge \text { let } \mathrm{z}: \mathrm{X}^{\prime} \text { in } \llbracket \mathrm{X}: \mathrm{z} \rrbracket\right] \cdot\left(\mathrm{z}: \mathrm{X}^{\prime}\right) \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket  \tag{1}\\
\equiv & \text { let } \mathrm{z}: \forall \mathrm{X}^{\prime}\left[\exists \mathrm{X} \cdot\left(\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket \wedge \mathrm{X} \leq \mathrm{X}^{\prime}\right)\right] \cdot \mathrm{X}^{\prime} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket  \tag{2}\\
\equiv & \text { let } \mathrm{z}: \forall \mathrm{X}^{\prime}\left[\llbracket \mathrm{t}_{1}: \mathrm{X}^{\prime} \rrbracket\right] \cdot \mathrm{X}^{\prime} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket  \tag{3}\\
\equiv & \llbracket \text { let } \mathrm{z}=\mathrm{t}_{1} \text { in } \mathrm{t}_{2}: \mathrm{T} \rrbracket \tag{4}
\end{align*}
$$

where (1) is by definition of constraint generation for match; (2) is by definition of constraint generation for patterns, by C-InID, C-IN*, and C-LETEx; (3) is by Lemma $1.6 .4 ;(4)$ is by definition of constraint generation for let.

1.9.26 Solution: The type scheme $\forall \overline{\mathrm{X}} . \mathrm{T} \rightarrow \mathrm{T}$ may be written $\forall \overline{\mathrm{X}}$. $[\mathrm{X} \mapsto \mathrm{T}](\mathrm{X} \rightarrow \mathrm{X})$. Furthermore, $\overline{\mathrm{X}} \# \forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$ holds. Thus, $\forall \overline{\mathrm{X}} . \mathrm{T} \rightarrow \mathrm{T}$ is an instance of $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$
in the sense of DM-INST'. Since DM-InsT' is an admissible rule for the type system DM, and since it is clear that the identity function $\lambda z . z$ has type $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$, it must also have type $\forall \overline{\mathrm{X}} . \mathrm{T} \rightarrow \mathrm{T}$. (A more direct proof of this fact would not be difficult.) So, the destructor $(\cdot: \exists \overline{\mathrm{X}} . \mathrm{T})$ has not only identity semantics, but also an identity type. This shows that our definitions are sound.

Let us now check requirement (i) of Definition 1.7.6. Since R-Annotation is pure, it suffices to show that let $\Gamma_{0}$ in $\llbracket(\mathrm{v}: \exists \overline{\mathrm{X}} . \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ entails let $\Gamma_{0}$ in $\llbracket \mathrm{v}: \mathrm{T}^{\prime} \rrbracket$.

Now, we have

$$
\begin{array}{ll} 
& \text { let } \Gamma_{0} \text { in } \llbracket(\mathrm{v}: \exists \overline{\mathrm{X}} . \mathrm{T}): \mathrm{T}^{\prime} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{X} \overline{\mathrm{X}} \cdot\left(\mathrm{T} \rightarrow \mathrm{T} \leq \mathrm{X} \rightarrow \mathrm{T}^{\prime} \wedge \llbracket \mathrm{v}: \mathrm{X} \rrbracket\right) \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{X} \overline{\mathrm{X}} \cdot\left(\mathrm{X} \leq \mathrm{T} \leq \mathrm{T}^{\prime} \wedge \llbracket \mathrm{v}: \mathrm{X} \rrbracket\right) \\
\Vdash & \text { let } \Gamma_{0} \text { in } \llbracket \mathrm{v}: \mathrm{T}^{\prime} \rrbracket \tag{3}
\end{array}
$$

where (1) is by definition of constraint generation and by definition of $\Gamma_{0}((\cdot$ : $\exists \overline{\mathrm{X}} . \mathrm{T})$ ); (2) is by C-ArRow; and (3) follows from Lemma 1.6.3 and C-EX*.

\subsection*{1.10.5 Solution: We have}

$$
\begin{align*}
& \text { let } \Gamma_{0} \text { in } \exists \mathrm{z} \cdot \llbracket(\lambda \mathrm{z} \cdot \mathrm{z} \hat{+} \hat{1}: \forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}): \mathrm{Z} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{z} \cdot(\forall \mathrm{x} \cdot \llbracket \lambda \mathrm{z} \cdot \mathrm{z} \hat{+}: \mathrm{X} \rightarrow \mathrm{X} \rrbracket \wedge \exists \mathrm{X} .(\mathrm{X} \rightarrow \mathrm{X} \leq \mathrm{z}))  \tag{1}\\
\equiv & \text { let } \Gamma_{0} \text { in } \forall \mathrm{x} . \text { let } \mathrm{z}: \mathrm{x} \text { in } \llbracket \mathrm{z} \hat{+} \hat{1}: \mathrm{x} \rrbracket  \tag{2}\\
\equiv & \forall \mathrm{x} .(\text { int } \rightarrow \text { int } \rightarrow \text { int } \leq \mathrm{X} \rightarrow \text { int } \rightarrow \mathrm{X})  \tag{3}\\
\equiv & \forall \mathrm{x} .(\mathrm{X}=\text { int })  \tag{4}\\
\equiv & \text { false } \tag{5}
\end{align*}
$$

where (1) is by definition of constraint generation for universal type annotations; (2) is obtained by restricting the scope of $\exists \mathrm{Z}$ to the second conjunct, then dropping the latter altogether, since it is equivalent to true, and by Lemma 1.6.5; (3) is obtained by definition of constraint generation, by definition of $\Gamma_{0}(\hat{+})$ and of $\Gamma_{0}(\hat{1})$, and by a few simple equivalence laws; (4) follows from C-ARrow and antisymmetry of subtyping; (5) follows from the fact that int and (say) int $\rightarrow$ int have distinct interpretations, since the type constructors int and $\rightarrow$ are incompatible. On the other hand, we have

$$
\begin{align*}
& \text { let } \Gamma_{0} \text { in } \exists \mathrm{Z} \cdot \llbracket(\lambda \mathrm{z} \cdot \mathrm{z}: \forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}): \mathrm{Z} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \forall \mathrm{X} . \text { let } \mathrm{z}: \mathrm{X} \text { in } \llbracket \mathrm{z}: \mathrm{X} \rrbracket  \tag{1}\\
\equiv & \forall \mathrm{X} .(\mathrm{X} \leq \mathrm{X})  \tag{2}\\
\equiv & \text { true } \tag{3}
\end{align*}
$$

where (1) is obtained as above; (2) by definition of constraint generation, C-InID and C-IN*; (3) is by reflexivity of subtyping.

1.10.6 Solution: Under the naïve constraint generation rule for universal type variable introduction, the constraint $\llbracket \forall \mathrm{X} .(\lambda \mathrm{z} \cdot \mathrm{z}: \mathrm{X} \rightarrow \mathrm{X}): \mathrm{Z} \rrbracket$ is equivalent to $\forall \mathrm{X} .(\llbracket \lambda z . z: X \rightarrow X \rrbracket \wedge \mathrm{X} \rightarrow \mathrm{X} \leq \mathrm{Z})$. Since the first conjunct is a tautology, this is in turn equivalent to $\forall \mathrm{X}$. $(\mathrm{X} \rightarrow \mathrm{X} \leq \mathrm{Z}$ ). In a nondegenerate free term model where subtyping is interpreted as equality, this constraint is unsatisfiable. In a non-structural subtyping model equipped with a least type $\perp$ and a greatest type $\top$, it is equivalent to $\perp \rightarrow \top \leq \mathrm{Z}$. This is a pretty restrictive constraint: since no value has type $\perp$, a function whose type is (a supertype of) $\perp \rightarrow T$ cannot ever be invoked at runtime. This situation is clearly unsatisfactory. Checking that $\forall \mathrm{X} . \llbracket \lambda z . z: \mathrm{X} \rightarrow \mathrm{X} \rrbracket$ holds was indeed part of our intent, but constraining $\mathrm{Z}$ to be a supertype of $\mathrm{X} \rightarrow \mathrm{X}$ for every $\mathrm{X}$ was not.

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-150.jpg?height=56&width=1312&top_left_y=732&top_left_x=418)
$\overline{\mathrm{X}} \# \mathrm{ftv}\left(\mathrm{T}^{\prime}\right)$ (3). By (1), (2), (3), and by definition of constraint generation for local universal type annotations, $\llbracket(t: \forall \overline{\mathrm{X}} . \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ is well-defined and is $\forall \overline{\mathrm{X}} . \llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \exists \overline{\mathrm{X}} .\left(\mathrm{T} \leq \mathrm{T}^{\prime}\right)$ (4). By (3) and by definition of constraint generation for introduction of universal type variables and for general type annotations, $\llbracket \forall \overline{\mathrm{X}} .(\mathrm{t}: \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ is $\forall \overline{\mathrm{X}} \cdot \exists \mathrm{Z} .(\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{Z}) \wedge \exists \overline{\mathrm{X}} .\left(\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{T}^{\prime}\right)$, where $\mathrm{Z}$ is fresh, which we may immediately simplify to $\forall \overline{\mathrm{X}}$ $\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \exists \overline{\mathrm{X}}$. $\left(\llbracket t: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{T}^{\prime}\right)$ (5). Using C-ExAnd and Lemma 1.10.1, it is straightforward to check that (4) and (5) are equivalent.

1.10.9 Solution: We have

$$
\begin{array}{ll} 
& \exists \mathrm{Z} \cdot \llbracket \lambda \mathrm{z} \cdot \forall \mathrm{X} \cdot(\mathrm{z}: \mathrm{x}): \mathrm{z \rrbracket} \\
\Vdash & \exists \mathrm{Z}_{1} \mathrm{Z}_{2} \cdot \text { let } \mathrm{z}: \mathrm{Z}_{1} \text { in } \llbracket \forall \mathrm{X} .(\mathrm{z}: \mathrm{x}): \mathrm{Z}_{2} \rrbracket \\
\text { IF } & \exists \mathrm{Z}_{1} \cdot \forall \mathrm{X} \cdot\left(\mathrm{Z}_{1} \leq \mathrm{X}\right) \tag{2}
\end{array}
$$

where (1) is by definition of constraint generation for $\lambda$-abstractions, dropping the constraint that relates $\mathrm{Z}, \mathrm{Z}_{1}$, and $\mathrm{Z}_{2} ;(2)$ is by definition of constraint generation for universal type variable introduction, this time dropping information about $\mathrm{Z}_{2}$. Now, in a nondegenerate equality model, the constraint (2) is equivalent to false. In fact, for (2) to be satisfiable, the interpretation of subtyping must admit a least element $\perp$. We now see that $\llbracket \lambda z . \forall \mathrm{X} .(\mathrm{z}: \mathrm{X}): \mathrm{Z} \rrbracket$ is a very restrictive constraint. Indeed, it requires $z$ to have every type at once. Because $z$ is $\lambda$-bound-hence monomorphic-it must in fact have type $\perp$. On the other hand, we have

$$
\begin{align*}
& \exists \mathrm{Z} \cdot \llbracket \forall \mathrm{X} \cdot \lambda \mathrm{z} \cdot(\mathrm{z}: \mathrm{X}): \mathrm{Z} \rrbracket \\
\equiv & \forall \mathrm{x} \cdot \exists \mathrm{Z} \cdot \llbracket \lambda \mathrm{z} \cdot(\mathrm{z}: \mathrm{x}): \mathrm{Z} \rrbracket  \tag{1}\\
\equiv & \forall \mathrm{X} \cdot \exists \mathrm{ZZ} \mathrm{Z}_{1} \cdot\left(\mathrm{Z}_{2} \leq \mathrm{X} \wedge \mathrm{X} \leq \mathrm{Z}_{2} \wedge \mathrm{Z}_{1} \rightarrow \mathrm{Z}_{2} \leq \mathrm{Z}\right)  \tag{2}\\
\equiv & \text { true } \tag{3}
\end{align*}
$$
where (1) is by definition of constraint generation for universal type variable introduction, dropping the second conjunct, which is entailed by the first; (2) is by Lemma 1.6.5, by definition of constraint generation for general type annotations, and by a few simple equivalence laws; (3) follows from C-NAMEEQ and the witness substitution $\left[\mathrm{Z}_{1} \mapsto \mathrm{X}, \mathrm{Z}_{2} \mapsto \mathrm{X}, \mathrm{Z} \mapsto(\mathrm{X} \rightarrow \mathrm{X})\right]$.

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-151.jpg?height=43&width=484&top_left_y=545&top_left_x=758)

$$
\begin{aligned}
& \equiv \text { let } f: \forall x\left[\llbracket f i x f: S . \lambda z . t_{1}: x \rrbracket\right] . x \text { in } \llbracket t_{2}: T \rrbracket \\
& \equiv \text { let } f: \forall X\left[\text { let } f: S \text { in } \llbracket \lambda z . t_{1}: S \rrbracket \wedge S \preceq X\right] . X \text { in } \llbracket t_{2}: T \rrbracket \\
& \equiv \text { let } f: S \text { in } \llbracket \lambda z . t_{1}: S \rrbracket \wedge \text { let } f: \forall x[S \preceq x] . x \text { in } \llbracket t_{2}: T \rrbracket \\
& \equiv \text { let } f: S \text { in }\left(\llbracket \lambda z \cdot t_{1}: S \rrbracket \wedge \llbracket t_{2}: T \rrbracket\right)
\end{aligned}
$$

where (1) is by definition of the letrec syntactic sugar and by the definition of constraint generation for let constructs; we have $\mathrm{X} \notin f t v\left(\mathrm{~S}, \mathrm{t}_{1}\right)$; (2) is by definition of constraint generation for fix; (3) is by C-LETAND; (4) follows from the equivalence between the type schemes $\forall \mathrm{X}[\mathrm{S} \preceq \mathrm{X}] . \mathrm{X}$ and $\mathrm{S}$ - which itself is a direct consequence of C-ExTRAns-and from C-InAnd.

1.11.16 Solution: We reason simultaneously in both the subtyping model or the equal-only model, that is, we only rely on properties that are valid in both models.

We must first ensure that rules RD-DEFAULT, RD-Found, and RD-FolLow respect (Definition 1.7.5).
- Case RD-DEfault. The reduction is $\{\mathrm{v}\} .\{\ell\} \xrightarrow{\delta} \mathrm{v}$, which is pure. Therefore, it is sufficient to establish that let $\Gamma_{0}$ in $\llbracket\{\mathrm{v}\} \cdot\{\ell\}: \mathrm{T} \rrbracket$ entails let $\Gamma_{0}$ in $\llbracket \mathrm{v}: \mathrm{T} \rrbracket$. In fact, we have:

$$
\begin{array}{cc} 
& \text { let } \Gamma_{0} \text { in } \llbracket\{\mathrm{v}\} \cdot\{\ell\}: \mathrm{T} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XY} .(\cdot .\{\ell\} \preceq \mathrm{X} \rightarrow \mathrm{T} \wedge\{\cdot\} \preceq \mathrm{Y} \rightarrow \mathrm{X} \wedge \llbracket \mathrm{v}: \mathrm{Y} \rrbracket) \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XY} .\left(\exists \mathrm{X}_{1} \mathrm{X}_{2} \cdot\left(\Pi\left(\ell: \mathrm{X}_{1} ; \mathrm{X}_{2}\right) \rightarrow \mathrm{X}_{1} \leq \mathrm{X} \rightarrow \mathrm{T}\right)\right. \\
& \left.\wedge \exists \mathrm{Y}_{1} \cdot\left(\mathrm{Y}_{1} \rightarrow \Pi\left(\partial \mathrm{Y}_{1}\right) \leq \mathrm{Y} \rightarrow \mathrm{X}\right) \wedge \llbracket \mathrm{v}: \mathrm{Y} \rrbracket\right) \\
\Vdash & \text { let } \Gamma_{0} \text { in } \exists \mathrm{X}_{2} \mathrm{Y} .\left(\partial \mathrm{Y} \leq\left(\ell: \mathrm{X}_{1} ; \mathrm{X}_{2}\right) \wedge \mathrm{X}_{1} \leq \mathrm{T} \wedge \llbracket \mathrm{v}: \mathrm{Y} \rrbracket\right) \\
\Vdash & \text { let } \Gamma_{0} \text { in } \exists \mathrm{Y} .\left(\mathrm{Y} \leq \mathrm{X}_{1} \wedge \mathrm{X}_{1} \leq \mathrm{T} \wedge \llbracket \mathrm{v}: \mathrm{Y} \rrbracket\right) \\
\Vdash & \text { let } \Gamma_{0} \text { in } \llbracket \mathrm{v}: \mathrm{T} \rrbracket \tag{5}
\end{array}
$$

where (1) is by definition of constraint generation; (2) is by definition of $\Gamma_{0}$, C-InId; (3) by variances of $\Pi, \ell$, and $\rightarrow$, C-And, C-Ex*, C-ExAnd; (4) by C-Row-DL and covariance of $\ell$; (5) by Lemma 1.6.3.

○ Case RD-Found: The reduction is $\{\mathrm{w}$ with $\ell=\mathrm{v}\} .\{\ell\} \xrightarrow{\delta} \mathrm{v}$. It suffices to establish let $\Gamma_{0}$ in $\llbracket\{\mathrm{w}$ with $\ell=\mathrm{v}\} \cdot\{\ell\}: \mathrm{T} \rrbracket$ entails let $\Gamma_{0}$ in $\llbracket \mathrm{v}: \mathrm{T} \rrbracket$. In fact, we
have:

$$
\begin{align*}
& \text { let } \Gamma_{0} \text { in } \llbracket\{\mathrm{w} \text { with } \ell=\mathrm{v}\} \cdot\{\ell\}: \mathrm{T} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XYY}^{\prime} \cdot\left(\cdot:\{\ell\} \preceq \mathrm{X} \rightarrow \mathrm{T} \wedge\{\cdot \text { with } \ell=\cdot\} \preceq \mathrm{Y} \rightarrow \mathrm{Y}^{\prime} \rightarrow \mathrm{X} \wedge\right. \\
\wedge & \left.\wedge \llbracket \mathrm{w}: \mathrm{Y} \rrbracket \wedge \llbracket \mathrm{v}: \mathrm{Y}^{\prime} \rrbracket\right)  \tag{1}\\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XYY}^{\prime} \cdot\left(\exists \mathrm{X}_{1} \mathrm{X}_{2} \cdot\left(\Pi\left(\ell: \mathrm{X}_{1} ; \mathrm{X}_{2}\right) \rightarrow \mathrm{X}_{1} \leq \mathrm{X} \rightarrow \mathrm{T}\right)\right. \\
& \wedge \exists \mathrm{Y}_{1} \mathrm{Y}_{2} \mathrm{Y}_{3} \cdot\left(\Pi\left(\ell: \mathrm{Y}_{1} ; \mathrm{Y}_{3}\right) \rightarrow \mathrm{Y}_{2} \rightarrow \Pi\left(\ell: \mathrm{Y}_{2} ; \mathrm{Y}_{3}\right) \leq \mathrm{Y} \rightarrow \mathrm{Y}^{\prime} \rightarrow \mathrm{X}\right) \\
& \left.\wedge \llbracket \mathrm{w}: \mathrm{Y} \rrbracket \wedge \llbracket \mathrm{v}: \mathrm{Y}^{\prime} \rrbracket\right)  \tag{2}\\
I & \text { let } \Gamma_{0} \text { in } \exists \mathrm{Y}^{\prime} \mathrm{X}_{1} \mathrm{Y}_{2} \cdot\left(\mathrm{Y}^{\prime} \leq \mathrm{Y}_{2} \wedge \mathrm{Y}_{2} \leq \mathrm{X}_{1} \wedge \mathrm{X}_{1} \leq \mathrm{T} \wedge \llbracket \mathrm{v}: \mathrm{Y}^{\prime} \rrbracket\right)  \tag{3}\\
I & \text { let } \Gamma_{0} \text { in } \llbracket \mathrm{v}: \mathrm{T} \rrbracket \tag{4}
\end{align*}
$$

where (1) is by definition of constraint generation; (2) is by definition of $\Gamma_{0}$, C-InID; (3) by variances of $\Pi, \ell$, and $\rightarrow$, C-And, C-Ex*, C-ExAnd; (4) by Lemma 1.6.3.
- Case RD-Follow The proof is similar to the previous case.

We must now check that if the configuration $F \mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$ is is well-typed, then either it is reducible, or it is a value.

We begin by checking that every value that is well-typed with type $\Pi \mathrm{T}$ is a record value, that is, either of the form $\left\{\mathrm{v}^{\prime}\right\}$ or $\left\{\mathrm{v}^{\prime \prime}\right.$ with $\left.\ell^{\prime}=\mathrm{v}^{\prime}\right\}$. Indeed, suppose that let $\Gamma_{0}$ in $\llbracket \mathrm{v}: \Pi \mathrm{T} \rrbracket$ is satisfiable. Then, $v$ cannot be a program variable, for a well-typed value must be closed; $v$ cannot be a memory location $m$, for otherwise ref $M(m) \leq \Pi \mathrm{T}$ would be satisfiable - but the top type constructors ref and $\Pi$ are incompatible (since $\Pi$ is isolated); v cannot be a partial application of a constructor or a primitive, nor a $\lambda$-abstraction, since otherwise $\mathrm{T}^{\prime} \rightarrow \mathrm{T}^{\prime \prime} \leq \Pi \mathrm{T}$ would be satisfiable but the top type constructors $\rightarrow$ and $\Pi$ are incompatible (since they are both isolated); thus v must either be of the form $\{\mathrm{v}\}$ or $\{\mathrm{w}$ with $\ell=\mathrm{v}\}$, for these are the only left cases.

Next, we note that, according to the constraint generation rules, if the configuration $\mathrm{c}_{1} \ldots \mathrm{v}_{k} / \mu$ is well-typed, then a constraint of the form let $\Gamma_{0} ; \operatorname{ref} M$ in $\left(\mathrm{c} \preceq \mathrm{x}_{1} \rightarrow \ldots \rightarrow \mathrm{x}_{k} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}_{1}: \mathrm{x}_{1} \rrbracket \wedge \ldots \wedge \llbracket \mathrm{v}_{k}: \mathrm{x}_{k} \rrbracket\right)$ is satisfiable. We now reason by cases on $\mathrm{c}$.

$\circ$ Case $\mathrm{c}$ is $\{\cdot\}$. We may asume $k \geq 2$, since otherwise, the expression is a value. Then $\Gamma_{0}(\mathrm{c})$ is $\forall \mathrm{XY} . \mathrm{X} \rightarrow \Pi(\partial \mathrm{X})$, so by C-INID and C-ARROw the above constraint entails $\exists \mathrm{X} .\left(\Pi(\partial \mathrm{X}) \leq \mathrm{X}_{2} \rightarrow \ldots \rightarrow \mathrm{T}\right)$, which by C-Class-I entails false since $\rightarrow$ and $\Pi$ are imcompatible. Thus, this case cannot occur.

$\circ$ Case $\mathrm{c}$ is $\{\cdot$ with $\ell=\cdot\}$. Similar to the previous case.

$\circ$ Case $\mathrm{c}$ is $\cdot\{\ell\}$. We may asume $k \geq 1$, since otherwise, the expression is a value. Then $\Gamma_{0}(\mathrm{c})$ is $\forall \mathrm{XY} . \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}$, so by C-INID and C-ARRow the above constraint entails let $\Gamma_{0} ; \operatorname{ref} M$ in $\left(\exists \mathrm{XY} .\left(\mathrm{X}_{1} \leq \Pi(\ell: \mathrm{X} ; \mathrm{Y})\right) \wedge \llbracket \mathrm{v}_{1}: \mathrm{X}_{1} \rrbracket\right)$, which by lemma 1.6.3 entails let $\Gamma_{0} ; \operatorname{ref} M$ in $\exists \mathrm{XY} . \llbracket \mathrm{v}_{1}: \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rrbracket$. Thus $\mathrm{v}_{1}$ is a record value, that is, either of the form $\left\{\mathrm{v}^{\prime}\right\}$ and the configuration is reducible
to $\mathrm{v}^{\prime}$ or of the form $\left\{\mathrm{v}^{\prime \prime}\right.$ with $\left.\ell^{\prime}=\mathrm{v}^{\prime}\right\}$ and the configuration is reducible to either $\mathrm{v}^{\prime}$ or $\mathrm{v}^{\prime \prime} .\{\ell\}$.

1.11.17 Solution: We add a collection of destructors $\cdot\left[\ell_{1} \leftrightarrow \ell_{2}\right]$ of arity 1 for all pairs of distinct labels, with the following semantics:

$$
\begin{array}{rr}
\{\mathrm{v}\}\left[\ell_{1} \leftrightarrow \ell_{2}\right] \xrightarrow{\delta} \mathrm{v} \\
\{\mathrm{w} \text { with } \ell=\mathrm{v}\}\left[\ell_{1} \leftrightarrow \ell_{2}\right] \xrightarrow{\delta}\left\{\mathrm{w}\left[\ell_{1} \leftrightarrow \ell_{2}\right] \text { with } \ell=\mathrm{v}\right\} & \text { if } \ell \notin\left\{\ell_{1}, \ell_{2}\right\} \\
\{\mathrm{w} \text { with } \ell=\mathrm{v}\}\left[\ell_{1} \leftrightarrow \ell_{2}\right] \xrightarrow{\delta}\left\{\mathrm{w}\left[\ell_{1} \leftrightarrow \ell_{2}\right] \text { with } \bar{\ell}=\mathrm{v}\right\} & \text { if }\{\ell, \bar{\ell}\}=\left\{\ell_{1}, \ell_{2}\right\}
\end{array}
$$

The initial environment $\Gamma_{0}$ must be extended with the following typing asumption:

$$
\cdot\left[\ell_{1} \leftrightarrow \ell_{2}\right]: \quad \forall \mathrm{X}_{1} \mathrm{X}_{2} \mathrm{Y} \cdot \Pi\left(\ell_{1}: \mathrm{X}_{1} ; \ell_{2}: \mathrm{X}_{2} ; \mathrm{Y}\right) \rightarrow \Pi\left(\ell_{1}: \mathrm{X}_{2} ; \ell_{2}: \mathrm{X}_{1} ; \mathrm{Y}\right)
$$

We must then check subjection reduction for the new primitive. Since we only added a constructor, it sufficies to check progress for the new primitive, that is, that well-typed expressions of the form $\left[\ell_{1} \leftrightarrow \ell_{2}\right] \mathrm{v}_{1} \ldots \mathrm{v}_{n}$ are either value or can be further reduced. Both parts are easy and similar to the corresponding parts in Exercice 1.11.16.

1.11.18 Solution: There are several solutions. One of them is to asume a fixed total ordering on row-labels, and to retain as constructors only $\ell^{\kappa, L}$ such that $\ell<L$, that is $\ell<\ell^{\prime}$ for all $\ell^{\prime} \in L$; other constants $\ell^{\kappa, L}$ such that $\ell \nless L$ are moved from constructors to the status of destructors with the following collection of reduction rules:

$$
\left\{\left\{\mathrm{w} \text { with } \ell^{\prime}=\mathrm{v}^{\prime}\right\} \text { with } \ell=\mathrm{v}\right\} \xrightarrow{\delta}\left\{\{\mathrm{w} \text { with } \ell=\mathrm{v}\} \text { with } \ell^{\prime}=\mathrm{v}^{\prime}\right\}
$$

(RD-TRANSPOSE)

for all labels $\ell$ and $\ell^{\prime}$ such that $\ell^{\prime}<\ell$ and

$$
\left\{\left\{\mathrm{w} \text { with } \ell=\mathrm{v}^{\prime}\right\} \text { with } \ell=\mathrm{v}\right\} \xrightarrow{\delta}\{\mathrm{w} \text { with } \ell=\mathrm{v}\}
$$

(RD-DISCARD)

for all labels $\ell$. It is now obvious that values are in normal forms, in the sense that explicit fields are never repeated and are always listed in order. Typing rules need not be changed, so requirement (i) of Definition 1.7.6 still holds. Requirement (ii) need to be check, in particular, for the new primitives $\ell^{L}$, which we leave to the reader (the proof for $\cdot .\{\ell\}$ should hold unchanged).

1.11.19 Solution: Let map have type $\Pi(\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow \Pi(\mathrm{X}) \rightarrow \Pi(\mathrm{Y})$, and the following reduction rules in the semantics with normal forms:

$$
\begin{gathered}
\operatorname{map}\left\{\mathrm{v}^{\prime} \text { with } \ell=\mathrm{v}\right\} \mathrm{w} \xrightarrow{\delta}\left\{\operatorname{map} \mathrm{v}^{\prime} \mathrm{w} \text { with } \ell=\mathrm{v}(\mathrm{w} \cdot\{\ell\})\right\} \\
\operatorname{map} \mathrm{v}\left\{\mathrm{w}^{\prime} \text { with } \ell=\mathrm{w}\right\} \xrightarrow{\delta}\left\{\operatorname{map} \mathrm{v} \mathrm{w}^{\prime} \text { with } \ell=(\mathrm{v} \cdot\{\ell\}) \mathrm{w}\right\} \\
\operatorname{map}\{\mathrm{v}\}\{\mathrm{w}\} \xrightarrow{\delta}\{\mathrm{v} \mathrm{w}\}
\end{gathered}
$$

1.11.22 Solution: To ensure that the field is not present in the argument of extension, it sufficies to restrict its the typing asumptions as follows:

$$
\langle\cdot \text { with } \ell=\cdot\rangle: \forall \mathrm{Xx}^{\prime} \mathrm{Y} . \Pi(\ell: \text { abs } ; \mathrm{Y}) \rightarrow \mathrm{X}^{\prime} \rightarrow \Pi\left(\ell: \text { pre } \mathrm{X}^{\prime} ; \mathrm{Y}\right)
$$

To remove an existing field, we can use the following syntactic sugar:

$$
\begin{aligned}
\cdot \backslash \ell \stackrel{\text { def }}{=} & \lambda \mathrm{v} \cdot\{\mathrm{v} \text { with } \ell=\mathrm{abs}\} \\
& : \forall \mathrm{XY} . \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rightarrow \Pi(\ell: \text { abs } ; \mathrm{Y})
\end{aligned}
$$

The following weaker typing asumption could also be used to ensure that the field is always present before removal:

$$
\forall X Y . \Pi(\ell: \text { pre } \mathrm{X} ; \mathrm{Y}) \rightarrow \Pi(\ell: \text { abs } ; \mathrm{Y})
$$

1.11.25 Solution: The proof is similar to 1.11 .16 but slightly more complex because we must also check that labels are defined when accessed, and with subtyping.

We reason simultaneously in both the subtyping model or the equal-only model, that is, we only rely on properties that are valid in both models.

We must first ensure that rules RE-FOUND and RE-FOLLOW respect (Definition 1.7.5).
- Case RE-Found: See Exercice ??. In line ??, field $\ell$ is pre $\mathrm{X}_{1}$ instead of $\mathrm{X}_{1}$ and pre $\mathrm{Y}_{2}$ instead of $\mathrm{Y}_{2}$ and step ?? also uses covariance of pre.
- Case RE-Follow The proof is similar.

We must then check that if the configuration $F \mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$ is is well-typed, then either it is reducible, or it is a value.

We begin by checking that every value that is well-typed with type $\Pi \mathrm{T}$ is a record value, that is, either of the form \langle\rangle or $\left\langle\mathrm{v}^{\prime \prime}\right.$ with $\left.\ell^{\prime}=\mathrm{v}^{\prime}\right\rangle$. See Exercice 1.11.16.

Next, we note that, according to the constraint generation rules, if the configuration $c v_{1} \ldots v_{k} / \mu$ is well-typed, then a constraint of the form let $\Gamma_{0} ; \operatorname{ref} M$ in $\left(\mathrm{c} \preceq \mathrm{x}_{1} \rightarrow \ldots \rightarrow \mathrm{x}_{k} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}_{1}: \mathrm{x}_{1} \rrbracket \wedge \ldots \wedge \llbracket \mathrm{v}_{k}: \mathrm{x}_{k} \rrbracket\right)$ is satisfiable. We now reason by cases on $\mathrm{c}$.

$\circ$ Case $\mathrm{c}$ is \langle\rangle or $\langle\cdot$ with $\ell=\cdot\rangle$. See Exercice 1.11.16.

$\circ$ Case $\mathrm{c}$ is $\cdot\langle\ell\rangle$. We may asume $k \geq 1$, since otherwise, the expression is a value. Then $\Gamma_{0}(\mathrm{c})$ is $\forall \mathrm{XY} . \Pi(\ell$ : pre $\mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}$, so by C-INID and C-ARRow the above constraint entails let $\Gamma_{0} ; \operatorname{ref} M$ in $\left(\exists \mathrm{XY} .\left(\mathrm{X}_{1} \leq \Pi(\ell:\right.\right.$ pre $\left.\left.\mathrm{X} ; \mathrm{Y})\right) \wedge \llbracket \mathrm{v}_{1}: \mathrm{X}_{1} \rrbracket\right)$, which by lemma 1.6.3 entails let $\Gamma_{0} ; \operatorname{ref} M$ in $\exists \mathrm{XY} . \llbracket \mathrm{v}_{1}: \Pi(\ell:$ pre $\mathrm{X} ; \mathrm{Y}) \rrbracket$. Thus $\mathrm{v}_{1}$ is a record value, that is, either of the form \langle\rangle or $\left\langle\mathrm{v}^{\prime \prime}\right.$ with $\left.\ell=\mathrm{v}^{\prime}\right\rangle$. In fact, the former case cannot occur, since let $\Gamma_{0} ; \operatorname{ref} M$ in $\exists X Y . \llbracket\langle\rangle: \Pi(\ell:$ pre X ; Y)】 entails $\exists X Y \Pi(\partial a b s) \leq \Pi(\ell$ : pre X; $)$ by C-INID and C-IN*, which in turns
entails $\exists$ X.abs $\leq$ pre $\mathrm{X}$ by C-Row-DL and covariance of $\Pi$ and $\ell$. However, this constraint is equivalent to false, because $\phi(\mathrm{abs}) \leq \phi$ (pre $\mathrm{X}$ ) does not hold in any ground assignment $\phi$. Thus $\mathrm{v}_{1}$ is $\left\langle\mathrm{v}^{\prime \prime}\right.$ with $\left.\ell^{\prime}=\mathrm{v}^{\prime}\right\rangle$ and the configuration is reducible to $\mathrm{v}^{\prime}$ if $\ell^{\prime}$ is $\ell$ or $\mathrm{v}^{\prime \prime}$ otherwise.