# $1 M L$ 

由François Pottier和Didier Rémy撰写

### 1.1 前言

名称与重命名

数学家和计算机科学家使用名称来指代定理陈述中的任意或未知对象，指代函数的参数等。名称之所以方便，是因为它们能够被人理解；然而，它们也可能具有欺骗性。关于名称及其重命名所涉及的困难进行深入探讨超出了本章的范围：我们建议读者研究Gabbay和Pitts的优秀系列论文（Gabbay和Pitts，2002；Pitts，2002b）。在这里，我们仅仅回顾本章中使用的几个概念。例如，考虑一个简单编程语言的抽象语法归纳定义，即纯λ-演算：

$$
\mathrm{t}::=\mathrm{z}|\lambda \mathrm{z} . \mathrm{t}| \mathrm{t} \mathrm{t}
$$

在这里，元变量 $\mathrm{z}$ 范围在一个无限变量的集合上——也就是说，名称——而元变量 t 范围在项上。与数学中通常的做法一样，我们写“变量 $z$ ”和“项 $t$ ”，而不是“由 $z$ 表示的变量”和“由 t 表示的项”。上述定义指出，一个项可以是变量 $\mathbf{z}$，一个变量和项的二元组，写作 $\lambda$ z.t，或者是两个项的二元组，写作 $t_{1} t_{2}$。然而，这并不是我们真正需要的。实际上，根据这个定义，项 $\lambda z_{1} \cdot z_{1}$ 和 $\lambda z_{2} \cdot z_{2}$ 是不同的，而我们希望它们是同一个数学对象，因为我们打算让 $\lambda z . z$ 表示“将 $z$ 映射到 $z$ 的函数”——这个含义与名称 $z$ 无关。为了达到这个效果，我们通过声明构造 $\lambda$ z.t 在 $t$ 中绑定 $\mathbf{z}$ 来完善上述定义。也可以说 $\lambda \mathrm{z}$ 是一个绑定器，其作用域是 $t$。那么，$\lambda z . t$ 便不再是一个二元组：更确切地说，它是项 $t$ 中变量 $z$ 的抽象。抽象具有这样的性质：绑定变量的身份并不重要；即 $\lambda z_{1} . z_{1}$ 和 $\lambda z_{2} . z_{2}$ 是相同的项。非正式地说，我们认为项在 $\alpha$-转换下是等价的。一旦绑定器的作用域和位置已知，便会得出几个标准概念，例如项 $t$ 的自由变量集合，记作 $f v(t)$，以及在项 $t_{2}$ 中对变量 $z$ 进行避俘获替换的项 $t_{1}$，记作 $\left[\mathrm{z} \mapsto \mathrm{t}_{1}\right] \mathrm{t}_{2}$。为了简洁，我们写 $f v\left(\mathrm{t}_{1}, \mathrm{t}_{2}\right)$ 表示 $f v\left(\mathrm{t}_{1}\right) \cup f v\left(\mathrm{t}_{2}\right)$。如果一个项没有自由变量，它就被认为是闭项。

重命名是一个从变量到变量的完全双射映射，它只影响有限数量的变量。变量的唯一属性是它的身份，即它与其他变量不同的特性。因此，在全局层面，所有变量都是可互换的：如果一个定理在没有关于任何特定变量的假设下成立，那么它的任何重命名也同样成立。我们经常利用这个事实。在证明定理T时，我们说可以不妨假设假设H，如果没有失去一般性（w.l.o.g.），即从定理H => T通过重命名论证可以得到定理T，这通常是不言而喻的。

如果 $\bar{z}_{1}$ 和 $\bar{z}_{2}$ 是变量集，我们用 $\bar{z}_{1} \# \bar{z}_{2}$ 作为简写表示 $\overline{\mathrm{z}}_{1} \cap \overline{\mathrm{z}}_{2}=\varnothing$，并且说 $\overline{\mathrm{z}}_{1}$ 对于 $\overline{\mathrm{z}}_{2}$ 是新鲜的（反之亦然）。我们说 $\overline{\mathrm{z}}$ 对于 $t$ 是新鲜的，当且仅当 $\bar{z} \# \mathrm{fv}(\mathrm{t})$ 成立。

在本章中，我们处理几种不同的名称变体：程序变量、内存位置和类型变量，后者可能进一步分为种类。我们从不同的变体中抽取名称，这些变体来自互不相交的集合，每个集合都是无限的。

### 1.2 What is ML?

“ML”这个名字出现在七十年代末。那时它指的是一种通用编程语言，被用作定理证明器LCF（Gordon，Milner和Wadsworth，1979b）中的元语言（其名字由此而来）。从那时起，几种新的编程语言从中汲取灵感，每种语言都提供了几种不同的实现方式。那么，“ML”今天代表什么呢？

对于语义学家来说，“ML”可能代表一种编程语言，它具有一等函数、由积和和构成的数据结构、可变内存单元（称为引用）、异常处理、自动内存管理和按值调用的语义。这种观点涵盖了标准ML（Milner、Tofte和Harper，1990年）和Caml（Leroy，2000年）系列的编程语言。我们将其称为$M L$-编程语言。

对于类型理论家来说，“ML”可能代表一类基于简单类型$\lambda$-演算的类型系统，但通过let声明引入了一种简单的多态性进行扩展。这些类型系统具有可决定的类型推断；它们的类型推断算法关键依赖于一阶统一，实际上可以变得高效。除了标准ML和Caml之外，这种观点还包括像Haskell（Hudak, Peyton Jones, Wadler, Boutel, Fairbairn, Fasel, Guzman, Hammond, Hughes, Johnsson, Kieburtz, Nikhil, Partain, 和Peterson, 1992）和Clean（Brus, van Eekelen, van Leer, 和Plasmeijer, 1987）这样的编程语言，它们的语义实际上有所不同——确实是纯粹且懒惰的——但它们的类型系统符合这个描述。我们将其称为$ML$-类型系统。在文献中，它也被称为Hindley和Milner的类型纪律。

对于我们来说，“ML”也可能指的是本章中给出并研究的一种特定编程语言的正式定义。它是一种核心演算，具有一等函数、let声明和常量。它配备了按值调用语义。通过定制常量及其语义，可以恢复数据结构、引用等。我们将这种特定的演算称为$M L$-演算。

为什么在今天，即在最初发现之后这么长的时间里还要学习ML类型系统？人们至少可以想到两个原因。

首先，它在文献中的处理往往很草率，因为它被认为要么是简单类型λ演算的简单扩展（TAPL第9章），要么是Girard和Reynolds的System F的一个子集（TAPL第23章）。前一种观点得到了这样的支持：let构造，它将ML类型系统与简单类型λ演算区分开来，可以被视为一种简单的文本扩展工具。然而，这种观点只讲述了部分故事，因为它没有解释ML类型系统所享有的主要类型属性，导致了一个时间复杂度为指数级的简单类型推断算法，并且在语言扩展了副作用（如状态或异常）时无法成立。后一种观点得到了这样的支持：ML类型系统内的每个类型推导也是隐性类型变体System F中有效的类型推导。这种观点是正确的，但同样没有为ML类型系统的类型推断提供解释，因为System F的类型推断是不可判定的（Wells，1999）。

其次，关于ML类型系统类型推断的现有账户（Milner, 1978; Damas和Milner, 1982; Tofte, 1988; Leroy, 1992; Lee和Yi, 1998;）

琼斯，1999年）通常涉及类型替换的大量操作。这种无处不在的类型替换使用往往相当晦涩。此外，类型推断算法的实际实现并没有明确地操作替换；相反，它们扩展了一个标准的一阶统一算法，其中术语在新方程发现时原地更新（休伊特，1976年）。因此，从这些描述中很难看出如何为ML类型系统编写一个高效的类型推断算法。然而，尽管计算机的速度越来越快，当ML类型系统扩展了代价昂贵的特性时，例如Objective Caml的对象类型（雷米和沃尤恩，1998年）或多态方法（加里格和雷米，1999年），效率仍然至关重要。

因为这些原因，我们认为有必要介绍一种专注于类型推断、力求既优雅又高效实现的ML类型系统。为了实现这些目标，我们不采用类型替换，而是强调约束，这带来了一系列优势。首先，约束允许以模块化的方式呈现类型推断，将其视为约束生成器和约束求解器的组合。这种分解使得我们能够在一方面单独推理程序何时是正确的，而在另一方面单独研究如何检查其正确性。这在简单类型化λ演算中早已成为标准（TAPL第22章），但据我们所知，尚未有人为ML类型系统提出这种做法。其次，通常很自然地将求解器定义为约束重写系统。然后，约束语言不仅允许推理正确性——每个重写步骤是否保持意义？——还可以推理低级实现细节，因为约束是类型推断过程中操纵的数据结构。例如，用多元方程（Jouannaud和Kirchner，1991）描述统一性，可以推理内存中节点的共享，这是基于替换的方法无法解释的。最后，约束比类型替换更通用，可以描述ML类型系统的许多扩展，其中包括带有递归类型、行、子类型、混合前缀下的第一秩序统一性等等。

在深入探讨这种新型ML-类型系统呈现的细节之前，回顾其标准定义是很有必要的。因此，在以下内容中，我们首先定义编程语言ML-演算的语法和操作语义，并为其配备一个称为Damas和Milner类型系统的类型系统。

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-005.jpg?height=564&width=1520&top_left_y=223&top_left_x=222)

图1-1：ML-计算-calculus的语法

## ML-the-calculus

ML-λ-演算的语法定义在图1-1中。它由几个语法类别组成。

标识符将可能在程序中引用的几种名称分组：变量、内存位置和常量。我们让 $\mathrm{x}$ 和 $\mathrm{y}$ 表示标识符。变量（有时为了避免歧义被称为程序变量）是可以使用 $\lambda$ 或 let 绑定形式绑定到值的名称；换句话说，它们是函数参数或局部定义的名称。我们让 $z$ 和 $f$ 表示程序变量。有时我们用 _ 表示在其作用域内没有自由出现的程序变量：例如，$\lambda_{\text {_.t表示 }} \lambda$ z.t，前提是 $\mathrm{z}$ 对 $t$ 来说是新鲜的。内存位置是表示内存地址的名称。按照约定，内存位置永远不会出现在源程序中，即提交给编译器的程序。它们只在执行期间出现，当分配新的内存块时。常量是为原始值和操作固定的名称，例如整数字面量和整数算术操作。常量是有限或无限集合 $\mathcal{Q}$ 的元素。它们从不接受 $\alpha$-转换。程序变量、内存位置和常量属于不同的语法类别，绝不能混淆。

常量集合 $\mathcal{Q}$ 保持抽象，因此我们的大部分开发与它的具体定义独立。我们假设每个常量 $\mathrm{c}$ 都有一个非负整数序数 $a(\mathrm{c})$。我们进一步假设 $\mathcal{Q}$ 被划分为构造器子集 $\mathcal{Q}^{+}$ 和析构器子集 $\mathcal{Q}^{-}$。构造器和析构器的区别在于，前者用于形成值，而后者用于对值进行操作。

1.2.1 示例 [整数]：对于每一个整数 $n$，可以引入一个零元构造器 $\hat{n}$。此外，可以引入一个二元析构器 $\hat{+}$，其应用以中缀形式书写，因此 $t_{1} \hat{+} t_{2}$ 表示析构器 $\hat{+}$ 对表达式 $t_{1}$ 和 $t_{2}$ 的双重应用 $\hat{+} t_{1} t_{2}$。

表达式——也称为程序项或程序——是主要的语法类别。实际上，与诸如C和Java这样的过程式语言不同，包括ML编程语言在内的函数式语言取消了表达式和语句之间的区别。表达式包括标识符、λ-抽象、应用和局部定义。λ-抽象 λz.t 表示一个名为z的单个参数的函数，其结果是表达式t，换句话说，就是将z映射到t的函数。注意变量z在项t中是绑定的，因此（例如）λz1.z1和λz2.z2是相同的对象。应用 t1 t2 表示调用函数t1的实际参数t2的结果，或者换句话说，是应用t1到t2的结果。应用是左结合的，即t1 t2 t3代表(t1 t2) t3。构造 let z=t1 in t2 表示在将变量z绑定到t1之后评估t2的结果。注意变量z在t2中是绑定的，但在t1中不是，因此例如let z1=z1 in z1和let z2=z1 in z2是相同的对象。构造 let z=t1 in t2 与 (λz.t2) t1 含义相同，但ML类型系统以更灵活的方式处理它。总之，ML-演算的语法是纯λ-演算的语法，扩展了内存位置、常量和let构造。

值是表达式的子集。它们是计算已经完成的表达式。值包括标识符、λ-抽象以及常量的应用，形式为c v1 ... vk，其中k不超过c的元数（如果c是构造器），如果c是析构器，k小于c的元数。在接下来的讨论中，我们通常对闭值感兴趣，即不包含任何自由程序变量的值。我们使用元变量v和w表示值。

1.2.2 示例：整数字面量 $\ldots, \widehat{-1}, \hat{0}, \hat{1}, \ldots$ 是零元构造器，因此它们是值。整数加法 $\hat{+}$ 是二元析构器，所以它是一个值，每个部分应用 $\hat{+} \mathrm{v}$ 也是值。因此，$\hat{+} \hat{1}$ 和 $\hat{+} \hat{+}$ 都是值。将 $\hat{+}$ 应用于两个值，如 $\hat{2} \hat{+} \hat{2}$，不是值。

1.2.3 示例 [配对]：让 $(\cdot, \cdot)$ 成为二进制构造器。如果 $t_{1}$ 和 $t_{2}$ 都是表达式，那么双重应用 $(\cdot, \cdot) t_{1} t_{2}$ 可以称为 $t_{1}$ 和 $t_{2}$ 的配对，并且可以写成 $\left(t_{1}, t_{2}\right)$。根据上述定义，$\left(t_{1}, t_{2}\right)$ 是一个值当且仅当 $t_{1}$ 和 $t_{2}$ 都是值。

存储是内存位置到封闭值的有限映射。一个存储 $\mu$ 通常代表被称为堆的东西，即一组数据结构，每个数据结构在内存中都有一个特定的地址，并且可能包含指向堆中其他元素的指针。编程语言 ML 允许覆盖现有内存块的内容，这种操作有时被称为副作用。在操作语义中，这种效果通过将现有内存位置映射到新值来实现。我们用 $\varnothing$ 表示空存储。我们用 $\mu[m \mapsto \mathrm{v}]$ 表示将 $m$ 映射到 $\mathrm{v}$ 并在其他方面与 $\mu$ 一致的存储。当 $\mu$ 和 $\mu^{\prime}$ 具有不相交的定义域时，我们用 $\mu \mu^{\prime}$ 表示它们的并集。我们用 $\operatorname{dom}(\mu)$ 表示 $\mu$ 的定义域，用范围 $(\mu)$ 表示出现在其值域中的内存位置集合。

纯函数式语言的运算语义，比如纯λ-演算，可以作为表达式上的重写系统来定义。但是由于ML演算具有副作用，因此我们将其运算语义定义为配置上的重写系统。一个配置$t / \mu$是由一个表达式$t$和一个存储$\mu$组成的对。在$\mu$域中的内存位置被认为在$t / \mu$中是已绑定的，因此（例如）$m_{1} /\left(m_{1} \mapsto \hat{0}\right)$和$m_{2} /\left(m_{2} \mapsto \hat{0}\right)$是相同的对象。在下面的讨论中，我们通常对封闭配置感兴趣，即$t / \mu$这样的配置，使得$t$没有自由程序变量，并且$t$中或$\mu$范围内出现的每个内存位置都在$\mu$的域中。如果$t$是一个源程序，它的求值开始于一个空存储中——即，从配置$t / \varnothing$开始。按照惯例，源程序不包含内存位置，这是一个封闭配置。此外，我们将会看到，一个封闭配置的所有简化形式也都是封闭的。请注意，分离表达式和存储不是唯一的方法，也可以将存储片段作为表达式语法的一部分；这个想法，由（Crank和Felleisen, 1991）提出，类似于在进程演算中对引用单元的编码（Turner, 1995; Fournet和Gonthier, 1996）。

上下文是一个表达式，其中单个子表达式被替换成了一个洞，用[.]表示。评估上下文是上下文的一个严格子集。在评估上下文中，洞用来突出程序中可以应用简化规则的有效点。因此，评估上下文的定义确定了一个简化策略：它指出了简化步骤可能发生的位置和顺序。例如，$\lambda z$. $]$ 不是一个评估上下文的事实意味着函数体永远不会被评估——也就是说，除非函数被应用，见下面的R-BETA。事实上的 $t \mathcal{E}$ 只有当 $t$ 是一个值时才是一个评估上下文，这意味着，在评估应用 $t_{1} t_{2}$ 时，应该完全评估 $t_{1}$ 然后再尝试评估 $t_{2}$。更一般地说，在多重应用的情况下，这意味着应该从左到右评估参数。当然，也可以选择其他方案：例如，定义 $\mathcal{E}::=\ldots|\mathrm{t} \mathcal{E}| \mathcal{E} \mathrm{v} \mid \ldots$ 将强制从右到左的评估顺序，而定义 $\mathcal{E}::=\ldots \mid$ t $\mathcal{E}|\mathcal{E} \mathrm{t}| \ldots$ 会使得评估顺序未指定，实际上允许简化在两者之间交替进行。

| let $z=v$ in $t \longrightarrow[z \mapsto v] t$ | (R-BETA) <br> (R-LET) | $\mathrm{t} / \mu \longrightarrow \mathrm{t}^{\prime} / \mu^{\prime}$ <br> $\operatorname{dom}\left(\mu^{\prime \prime}\right) \# \operatorname{dom}\left(\mu^{\prime}\right)$ <br> $\frac{\operatorname{range}\left(\mu^{\prime \prime}\right) \# \operatorname{dom}\left(\mu^{\prime} \backslash \mu\right)}{\mathrm{t} / \mu \mu^{\prime \prime} \longrightarrow \mathrm{t}^{\prime} / \mu^{\prime} \mu^{\prime \prime}}$ | (R-ExtEnd) |
| :---: | :---: | :---: | :---: |
| $\frac{\mathrm{t} / \mu \xrightarrow{\delta} \mathrm{t}^{\prime} / \mu^{\prime}}{\mathrm{t} / \mu \longrightarrow \mathrm{t}^{\prime} / \mu^{\prime}}$ | (R-Delta) | $\frac{\mathrm{t} / \mu \longrightarrow \mathrm{t}^{\prime} / \mu^{\prime}}{\mathcal{E}[\mathrm{t}] / \mu \longrightarrow \mathcal{E}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}}$ | (R-CONTEXT) |

图1-2：ML-λ-演算的语义

两个子表达式，并使求值成为非确定性的。事实上，让 $\mathrm{z}=\mathrm{v}$ 在 $\mathcal{E}$ 中不是一个求值上下文，意味着局部定义的主体永远不会被求值 - 也就是说，直到定义本身被简化，见下面的 R-LET。我们用 $\mathcal{E}[\mathrm{t}]$ 表示用表达式 $t$ 替换 $\mathcal{E}$ 中的空位得到的表达式。

图1-2首先定义了配置之间的关系$\longrightarrow$，然后定义了封闭配置之间的关系。如果$\mathrm{t} / \mu \longrightarrow \mathrm{t}^{\prime} / \mu^{\prime}$或$\mathrm{t} / \mu \longrightarrow \mathrm{t}^{\prime} / \mu^{\prime}$成立，那么我们说配置$\mathrm{t} / \mu$简化为配置$\mathrm{t}^{\prime} / \mu^{\prime}$；这个定义中涉及的歧义是良性的。如果对于每个存储$\mu$，都有$t / \mu \longrightarrow t^{\prime} / \mu$成立，那么我们写作$\mathrm{t} \longrightarrow \mathrm{t}^{\prime}$，并且说这种简化是纯的。

关键简化规则是 $\mathrm{R}$-BETA，该规则指出函数应用 $(\lambda z . t) v$ 可简化为函数体，即 $t$，其中每个形式参数 $z$ 出现的地方都被实际参数 $v$ 替换。防止函数体 $t$ 被评估的 $\lambda$ 构造消失，因此新的项（通常）可以进一步简化。因为 ML-演算采用了按值调用策略，规则 R-BETA 只有在实际参数是一个值 $v$ 时才适用。换句话说，一个函数在其实际参数完全评估之前不能被调用。规则 R-LET 与 $\mathrm{R}$-BETA 非常相似。实际上，它规定 let $\mathrm{z}=\mathrm{v}$ in $\mathrm{t}$ 在简化方面与 $(\lambda z . t) v$ 具有相同的行为。我们注意到，在整个项中对程序变量进行值替换是昂贵的，因此 R-BETA 和 R-LET 从不按字面意思实现：它们只是一个简单的规范。实际实现通常使用运行时环境，这可以理解为一种显式替换形式（Abadi, Cardelli, Curien, 和 Lévy, 1991）。请注意，我们选择按值简化策略是相当任意的，并且对类型系统实质上没有影响；编程语言 Haskell （Hudak, Peyton Jones, Wadler, Boutel, Fairbairn, Fasel, Guzman, Hammond, Hughes, Johnsson, Kieburtz,）也是如此。

尼希尔、帕特恩和彼得森，1992年），其简化策略被称为懒惰或按需调用，也依赖于亨德利和米尔纳的类型纪律。

规则R-DELTA描述了常量的语义。它仅指出某个关系$\xrightarrow{\delta}$是$\longrightarrow$的一个子集。当然，由于常量集合未指定，关系$\xrightarrow{\delta}$也必须保持抽象。我们要求，如果$\mathrm{t} / \mu \xrightarrow{\delta} \mathrm{t}^{\prime} / \mu^{\prime}$成立，那么


（i）t具有形式cv1…vn，其中c是一个n元析构函数；以及

（ii） μ的定义域是μ'定义域的子集。

条件（i）确保 $\delta$-约简只涉及完全的应用析构函数，并且这些函数是根据按值调用策略进行求值的。条件（ii）确保 $\delta$-约简可以分配新的内存位置，但不能释放现有的位置。特别是，不能将“垃圾回收”运算符作为常量提供，因为它销毁不可达的内存单元。无论如何，在存在R-EXTEND的情况下这样做没有太大意义，R-EXTEND指出任何有效的约简在更大的存储中也是有效的。条件（ii）允许证明，如果 $t / \mu$ 约简到 $t^{\prime} / \mu^{\prime}$，那么 $\operatorname{dom}(\mu)$ 是 $\operatorname{dom}\left(\mu^{\prime}\right)$ 的一个子集；这留给读者作为一个练习。

1.2.4 示例 [整数，继续]: 整数加法的操作语义可以定义如下：

$$
\begin{equation*}
\hat{k}_{1} \hat{+} \hat{k}_{2} \xrightarrow{\delta} \widehat{k_{1}+k_{2}} \tag{R-ADD}
\end{equation*}
$$

左边的项是双重应用 $\hat{+} \hat{k}_{1} \hat{k}_{2}$，而右边的项是整数字面量 $\hat{k}$，其中 $k$ 是 $k_{1}$ 和 $k_{2}$ 的和。在这里需要区分对象级别和元级别（即 $\hat{k}$ 和 $k$ 之间的区别）以避免歧义。

1.2.5 示例 [对，继续]：除了在示例1.2.3中定义的对构造函数之外，我们可以引入两个一元析构函数 $\pi_{1}$ 和 $\pi_{2}$。我们可以按以下方式定义它们的操作语义，对于 $i \in\{1,2\}$ ：

$$
\begin{equation*}
\pi_{i}\left(\mathrm{v}_{1}, \mathrm{v}_{2}\right) \xrightarrow{\delta} \mathrm{v}_{i} \tag{R-PROJ}
\end{equation*}
$$

因此，我们对常量的处理足够通用，能够解释成对构造和销毁；我们无需将这些特性明确地构建到语言中。

1.2.6 练习 [布尔值，推荐，$\star \star$ ]：让true和false成为零元构造器。让if成为一个三元分解器。扩展操作语义。

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

让我们使用语法糖 if $t_{0}$ then $t_{1}$ else $t_{2}$ 来表示 if $t_{0} t_{1} t_{2}$ 的三次应用。解释一下这些定义为何没有提供预期行为。在不修改 if 的语义的情况下，建议一个新的语法糖 if $t_{0}$ then $t_{1}$ else $t_{2}$ 的定义，以纠正问题。

1.2.7 示例[和类型]：布尔值实际上可以看作是更一般和类型概念的一个特例。设 $inj_{1}$ 和 $inj_{2}$ 是一元构造器，分别称为左注入和右注入。设 case 是一个三元分解器，其语义定义如下，对于 $i \in \{1,2\}$ ：

$$
\begin{equation*}
\operatorname{case}\left(\mathrm{inj}_{i} \mathrm{v}\right) \mathrm{v}_{1} \mathrm{v}_{2} \xrightarrow{\delta} \mathrm{v}_{i} \mathrm{v} \tag{R-CASE}
\end{equation*}
$$

在这里，正在仔细审查值 $i n j_{i} \mathrm{v}$，而通常作为函数的值 $\mathrm{v}_{1}$ 和 $\mathrm{v}_{2}$ 代表标准情况构造的两个分支。规则根据审查的值是否是通过左注入或右注入形成的来选择适当的分支（此处为 $\mathrm{v}_{i}$）。分支 $\mathrm{v}_{i}$ 被执行，并被赋予访问注入携带的数据（此处为 v）的权限。

1.2.8 练习 $[\boldsymbol{\star}, \nrightarrow]$ ：解释如何用求和的方式编码真、假和if构造。检查R-TRUE和R-FALSE的行为是否被适当地模拟。

1.2.9 示例 [参考文献]：设 ref 和 ! 为一元析构器。设 $:=$ 为二元析构器。我们写 $t_{1}:=t_{2}$ 表示双重应用 $:=t_{1} t_{2}$。以下定义这三个析构器的操作语义：

$$
\begin{array}{rr}
\text { ref } \mathrm{v} / \varnothing \xrightarrow{\delta} m /(m \mapsto \mathrm{v}) \text { if } m \text { is fresh for } \mathrm{v} & (\mathrm{R}-\mathrm{REF}) \\
! m /(m \mapsto \mathrm{v}) \xrightarrow{\delta} \mathrm{v} /(m \mapsto \mathrm{v}) & \text { (R-DEREF) } \\
m:=\mathrm{v} /\left(m \mapsto \mathrm{v}_{0}\right) \xrightarrow{\delta} \mathrm{v} /(m \mapsto \mathrm{v}) & \text { (R-AssiGN) } \tag{R-AssiGN}
\end{array}
$$

根据R-REF规则，评估引用$v$时会分配一个全新的内存位置$m$并将$v$绑定到它上面。由于配置被认为是内存位置通过$\alpha$-转换相等，只要为$v$选择了新的名字$m$，这个名字的选择就是无关紧要的，这样可以防止意外捕获$v$中出现的自由内存位置。通过R-DEREF规则，评估$!m$将返回当前存储中绑定到内存位置$m$的值。通过$\mathrm{R}$-Assign规则，评估$m:=\mathrm{v}$会丢弃当前绑定到$m$的值$v_0$并生成一个新存储，其中$m$绑定到$v$。在这里，赋值$m:=\mathrm{v}$返回的值是$\mathrm{v}$本身；在ML编程语言中，它通常是一个无参构造器()，发音为unit。

1.2.10 示例[递归]：设fix是一个二元析构器，其操作语义为：

$$
\begin{equation*}
\mathrm{fixv}_{1} \mathrm{v}_{2} \xrightarrow{\delta} \mathrm{v}_{1}\left(\mathrm{fix}_{1}\right) \mathrm{v}_{2} \tag{R-FIX}
\end{equation*}
$$

fix是一个不动点组合子：它有效地允许函数的递归定义。实际上，ML编程语言提供的letrec $f=\lambda$ z. $_{1}$ in $t_{2}$构造可以被看作是语法糖，等价于let $f=$ fix $\left(\lambda f . \lambda z . t_{1}\right)$ in $t_{2}$。

规则R-CONTEXT通过定义闭配置之间的$\longrightarrow$关系来完成操作语义的定义，该关系是关于$\longrightarrow$的。该规则指出，规约不仅可以在项的根部发生，还可以在其深处发生，前提是从根部到规约发生点的路径形成了一个求值上下文。这就是求值上下文确定求值策略的方式。作为一个纯粹的技术点，由于$\longrightarrow$只与闭配置有关，我们不需要要求$\operatorname{dom}\left(\mu^{\prime} \backslash \mu\right)$中的内存位置对于$\mathcal{E}$来说是新的：实际上，在$\mathcal{E}$中出现的每个内存位置必须是$\operatorname{dom}(\mu)$的成员。

1.2.11 练习 $[\star \star \star$, 推荐, $\rightarrow$ a $]$ ：假设有布尔值和条件语句、整数字面量、减法、乘法、整数比较以及一个固定点组合子，其中大部分在之前的示例中定义过，定义一个计算其整数参数阶乘的函数，并将其应用于 $\hat{3}$。逐步确定这个表达式如何简化为一个值。

如果 $t / \mu$ 简化成 $t^{\prime} / \mu^{\prime}$，那么很容易检查出 $t$ 不是一个值。换句话说，值是不可简化的：它们代表一个完成的计算。证明留给读者作为一个练习。然而，反命题并不成立：如果 $t / \mu$ 关于 $\longrightarrow$ 是不可简化的，那么 $t$ 不一定是一个值。在这种情况下，配置 $t / \mu$ 称为卡住。它表示一个运行时错误，即一个不允许计算继续进行的情况，但并不被视为有效的结果。一个闭源程序 $\mathrm{t}$ 如果且仅当配置 $\mathrm{t} / \varnothing$ 简化成一个卡住的配置，才被认为是出错的。

1.2.12 示例：运行时错误通常发生在对预期之外的性质的参数应用析构器时。例如，表达式 $+1 \mathrm{~m}$ 和 $\pi_{1} \quad 2$ 以及 $! 3$ 无论当前存储状态如何都是卡住的。程序 let $\mathbf{z}=$ $\hat{+} \hat{+}$ in $z$ 并没有卡住，因为 $\hat{+} \hat{+}$ 是一个值。然而，通过 $\mathrm{R}$-LET 的简化是 $\hat{+} \hat{+}$，这是卡住的，所以这个程序出错。类型系统的主要目的是防止此类情况发生。

1.2.13 示例：如果$m$不在$\mu$的域中，那么配置$! m / \mu$就会卡住。然而在这种情况下，$! m / \mu$并不是闭合的。因为我们只将$\longrightarrow$视为闭合配置之间的关系，这种情况不可能出现。换句话说，ML-演算的语义决不允许悬空指针的产生。因此，无需采取特别的预防措施来防范它们。然而，一些强类型编程语言还是在受控的方式下允许悬空指针的存在（Tofte和Talpin，1997年；Crary，Walker和Morrisett，1999b年；DeLine和Fähndrich，2001年；Grossman，Morrisett，Jim，Hicks，Wang和Cheney，2002a年）。

达尔马斯和米尔纳的类型系统##

ML-类型系统最初由Milner（1978年）定义。在这里，我们重现了Damas和Milner（1982年）给出的定义，这个定义采用了更标准的风格：类型判断是通过一组类型规则归纳定义的。我们将这个类型系统称为DM。

首先，我们必须定义类型。在DM中，就像在简单类型的λ-演算中，类型是由类型构造器和类型变量构成的一阶项。我们从关于类型构造器的规范化的几个考虑开始。

首先，我们并不希望固定类型构造器的集合。当然，由于ML演算中有函数，我们需要能够用任意类型T和T'形成一个箭头类型T → T'；也就是说，我们需要一个二元类型构造器→。然而，由于ML演算包括一个未指明的常量集合，我们通常无法说得更具体。如果常量包括整数字面量和整数操作，如示例1.2.1中那样，那么需要一个零元类型构造器int；如果它们包括对构造和销毁，如示例1.2.3和1.2.5中那样，那么需要一个二元类型构造器×；依此类推。

其次，按位置引用类型构造器的参数是很常见的，也就是说，通过数字索引。例如，当人们写出 $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$ 时，理解类型构造器 $\rightarrow$ 的元数为2，$\mathrm{T}$ 是它的第一个参数，称为它的域，而 $\mathrm{T}^{\prime}$ 是它的第二个参数，称为它的陪域。然而，在这里，我们通过名称引用参数，这些名称称为方向。例如，我们定义了两个方向：域和陪域，并让类型构造器 $\rightarrow$ 具有元数 $\{$ 域，陪域 $\}$。在非结构子类型的定义（示例1.3.9）和行的定义（第1.11节）中利用了方向的这种额外的通用性。

最后，我们允许使用种类（kinds）对类型进行分类。因此，每个类型构造器不仅要有一个参数数量（arity），还要有一个更丰富的签名，描述它适用的类型的种类以及它产生的类型的种类。一个特殊的种类 $\star$ 与“正常”类型相关联，也就是说，这些类型是直接归因于表达式和值的。例如，类型构造器 $\rightarrow$ 的签名是 $\{$ domain $\mapsto \star$，codomain $\mapsto \star\}$ $\Rightarrow$ $\star$，因为它适用于两个“正常”类型并产生一个“正常”类型。

引入除 $\star$ 以外的种类允许我们将某些项视为不良形成的类型；例如，在1.11节中说明了这一点。然而，在最简单的情况下，$\star$ 真的是唯一的种类，因此类型构造函数的签名不过是其元数（一组方向），只要每个类型构造函数的应用尊重其元数，每个项都是一个良好形成的类型。

1.2.14 定义：令 $d$ 在有限或可数方向集合中取值。令 $\kappa$ 在有限或可数种类集合中取值。令 $\star$ 是一种特殊的种类。令 $K$ 在从方向到种类的部分映射集合中取值。令 $F$ 在有限或可数类型构造器的集合中取值，每个类型构造器都具有形如 $K \Rightarrow \kappa$ 的签名。$K$ 的定义域被称为 $F$ 的元数（arity），而 $\kappa$ 被称为它的像种类（image kind）。当 $K$ 为空时，我们写作 $\kappa$ 而不是 $K \Rightarrow \kappa$。令 $\rightarrow$ 是一个具有签名 $\{$ 定义域 $\mapsto \star$，值域 $\mapsto \star\} \Rightarrow \star$ 的类型构造器。

类型构造器和它们的签名共同构成了一个签名集 $\mathcal{S}$。在以下内容中，我们假设给定的一个固定签名 $\mathcal{S}$ 中的每个类型构造器都具有有限的元数，以确保类型可以被机器表示。然而，在1.11节中，我们将明确地处理几个不同的签名，其中一些涉及可枚举元的类型构造器。

类型变量是一个用来代表类型的名字。为了简单起见，我们认为每个类型变量都有一个种类标识，或者说，不同种类的类型变量来自于不重叠的集合。这些类型变量的每一个集合都单独受到α转换的约束：即，重命名必须保持种类不变。将种类附加到类型变量只是一个技术上的便利：实际上，在类型推断过程中执行的每个操作都保持了每个类型都是良好种类的属性，因此没有必要跟踪每个类型变量的种类。只需要检查用户提供的所有类型，在类型声明、类型注解或模块接口中，都是良好种类的。

1.2.15 定义：对于每一种类型$\kappa$，令$\mathcal{V}_{\kappa}$是一个不相交的可数类型变量集合。令$\mathrm{X}, \mathrm{Y}$和$\mathrm{Z}$在所有类型变量的集合$\mathcal{V}$中取值。令$\overline{\mathrm{X}}$和$\bar{Y}$在类型变量的有限集合中取值。我们用$\bar{X} \bar{Y}$表示集合$\bar{X} \cup \bar{Y}$，并且经常将$\mathrm{X}$写成单元素集合$\{\mathrm{X}\}$。我们用$f t v(o)$表示对象$o$的自由类型变量集合。

类型集合，由 $\mathrm{T}$ 表示，是自由多类型项代数，它源于类型构造器和类型变量。

1.2.16 定义：类型种类 $\kappa$ 要么是 $\mathcal{V}_{\kappa}$ 的一个成员，要么是形式为 $F\left\{d_{1} \mapsto \mathrm{T}_{1}, \ldots, d_{n} \mapsto \mathrm{T}_{n}\right\}$ 的项，其中 $F$ 的签名是 $\left\{d_{1} \mapsto \kappa_{1}, \ldots, d_{n} \mapsto \kappa_{n}\right\} \Rightarrow$ $\kappa$ 并且 $\mathrm{T}_{1}, \ldots, \mathrm{T}_{n}$ 分别是种类 $\kappa_{1}, \ldots, \kappa_{n}$ 的类型。

作为一种记号约定，我们假设对于每个类型构造器$F$，构成$F$的箭头 arity 是隐含有序的，因此我们可以说$F$具有签名$\kappa_{1} \otimes \ldots \otimes \kappa_{n} \Rightarrow \kappa$，并使用语法$F \mathrm{~T}_{1} \ldots \mathrm{T}_{n}$来表示$F$的应用。类型构造器$\rightarrow$的应用写成中缀形式，并且与右侧结合，所以$\mathrm{T} \rightarrow \mathrm{T}^{\prime} \rightarrow \mathrm{T}^{\prime \prime}$代表$\mathrm{T} \rightarrow\left(\mathrm{T}^{\prime} \rightarrow \mathrm{T}^{\prime \prime}\right)$。

为了给类型中的自由类型变量，或者更一般地说，类型判断中的自由类型变量赋予意义，包括Damas和Milner在内的传统ML类型系统表示法都采用了类型替换。我们的大部分表示法避免了替换，转而使用约束。然而，在某些情况下，我们确实需要替换，特别是在将我们的表示法与Damas和Milner的相联系时。

1.2.17 定义：类型替换 $\theta$ 是一种全局的、保持类型的映射，它将类型变量映射到类型上，在除了 $\mathcal{V}$ 的一个有限子集外的所有地方都是恒等映射，我们将这个子集称为 $\theta$ 的定义域，记作 $\operatorname{dom}(\theta)$。$\theta$ 的值域，我们记作 range $(\theta)$，是集合 $\operatorname{ftv}(\theta(\operatorname{dom}(\theta)))$。类型替换可以自然地被视为一种全局的、保持类型的映射，将类型映射到类型上。在以下内容中，我们记 $\overline{\mathrm{X}} \# \theta$ 为 $\overline{\mathrm{X}} \#(\operatorname{dom}(\theta) \cup$ range $(\theta))$。我们记 $\theta \backslash \overline{\mathrm{X}}$ 为 $\theta$ 在 $\overline{\mathrm{X}}$ 外的限制，即 $\theta$ 在 $\mathcal{V} \backslash \overline{\mathrm{X}}$ 上的限制。有时我们让 $\varphi$ 表示一个类型替换。

如果$\vec{X}$和$\vec{T}$分别是不同类型变量的向量和相同（有限）长度的类型向量，使得对于每个索引$i$，$\mathrm{x}_{i}$和$\mathrm{T}_{i}$具有相同的种类，那么$[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}]$表示将$\mathrm{X}_{i}$替换为$\mathrm{T}_{i}$的替换，对于每个索引$i$。$[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}]$的定义域是向量$\overrightarrow{\mathrm{X}}$底层集合$\overline{\mathrm{X}}$的子集。其值域是$f t v(\overline{\mathrm{T}})$的子集，其中$\overline{\mathrm{T}}$是向量$\vec{T}$底层集合。每个替换$\theta$可以写成$[\vec{X} \mapsto \vec{T}]$的形式，其中$\overline{\mathrm{X}}=\operatorname{dom}(\theta)$。然后，$\theta$是幂等的当且仅当$\overline{\mathrm{X}} \# \mathrm{ftv}(\overline{\mathrm{T}})$成立。

正如早先所指出的，类型是一阶项；也就是说，在类型的语法中，没有任何产生式绑定类型变量。因此，在类型T中出现每个类型变量在T中都是自由出现的。这种情况与简单类型λ-演算中的情况完全相同。当我们引入类型方案时，事情变得更加有趣。顾名思义，类型方案可能描述整个类型族；这种效果是通过类型变量的全体量化来实现的。

1.2.18 定义：类型方案 $\mathrm{S}$ 是形如 $\forall \overline{\mathrm{X}}$. $\mathrm{T}$ 的对象，其中 $\mathrm{T}$ 是种类为 $\star$ 的类型，类型变量 $\overline{\mathrm{X}}$ 在 $\mathrm{T}$ 中被视为绑定。

可以将类型$\mathrm{T}$视为平凡的类型方案$\forall \varnothing$。$\mathrm{T}$中没有普遍量化类型变量，因此类型可以被看作是类型方案的一个子集。类型方案$\forall \bar{X} . T$可以被视为描述可能形式为$[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$的无限类型家族的一种有限方式，其中$\overrightarrow{\mathrm{T}}$是任意的。

| $\Gamma(\mathrm{x})=\mathrm{S}$ | $(\mathrm{DM}-\mathrm{VAR})$ | $\Gamma \vdash \mathrm{t}_{1}: \mathrm{s}$ | $\Gamma ; \mathrm{z}: \mathrm{S} \vdash \mathrm{t}_{2}: \mathrm{T}$ | (DM-LET) |
| :---: | :---: | :---: | :---: | :---: |
| $\overline{\Gamma \vdash \mathrm{x}: \mathrm{S}}$ |  | $\overline{\Gamma \vdash \text { let } z=t_{1} \text { in } t_{2}: T}$ |  |  |
| $\Gamma ; \mathrm{z}: \mathrm{T} \vdash \mathrm{t}: \mathrm{T}^{\prime}$ | $(\mathrm{DM}-\mathrm{ABS})$ | $\Gamma \vdash \mathrm{t}: \mathrm{T}$ | $\overline{\mathrm{x}} \# \mathrm{ftv}(\Gamma)$ | (DM-GEN) |
| $\overline{\Gamma \vdash \lambda z . t: \mathrm{T} \rightarrow \mathrm{T}^{\prime}}$ |  | {$\Gamma \vdash \mathrm{t}: \forall \mathrm{X} . \mathrm{T}$ <br> $\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{X}} . \mathrm{T}$ <br> $\Gamma \vdash \mathrm{t}:[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$} |  |  |
| ![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-015.jpg?height=73&width=453&top_left_y=490&top_left_x=312) | (DM-APP) |  |  | (DM-INST) |
| $\Gamma \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}$ |  |  |  |  |

图1-3：DM的输入规则

这类类型被称为类型方案 $\forall \bar{X}$.T 的实例。请注意，在本章的大部分内容中，我们处理的是受限类型方案，这是 DM 类型方案（定义 1.3.2）的泛化。

输入环境，或简称环境，用于收集关于表达式自由标识符的假设。

1.2.19 定义：环境 $\Gamma$ 是一个有限的有序对序列，每对由程序标识符和类型模式组成。我们用 $\varnothing$ 表示空环境，用 ; 表示环境的连接。环境可以被视为一个从程序标识符到类型模式的有限映射，如果 $\Gamma$ 是形如 $\Gamma_{1} ; \mathrm{x}: \mathrm{S} ; \Gamma_{2}$ 的形式，并且 $\Gamma_{2}$ 中没有关于 $\mathrm{x}$ 的假设，则记作 $\Gamma(\mathrm{x})=\mathrm{S}$。环境 $\Gamma$ 的已定义程序标识符集合，记作 $d p i(\Gamma)$，定义为 $d p i(\varnothing)=\varnothing$ 和 $d p i(\Gamma ; \mathrm{x}: \mathrm{S})=d p i(\Gamma) \cup\{\mathrm{x}\}$。

为了完成Damas和Milner的类型系统的定义，还需要定义类型判断。一个类型判断具有形式 $\Gamma \vdash \mathrm{t}: \mathrm{S}$，其中 $\mathrm{t}$ 是我们关注的表达式，$\Gamma$ 是一个环境，通常包含关于 t 的自由程序标识符的假设，而 $\mathrm{S}$ 是一个类型方案。这样的判断可以这样读：在假设 $\Gamma$ 下，表达式 $\mathrm{t}$ 具有类型方案 $\mathrm{S}$。语言上的滥用，有时会说 $\mathrm{t}$ 有类型 $\mathrm{S}$。类型判断是有效的（或成立），当且仅当它可以使用图1-3中出现的规则来推导。表达式 t 在环境 $\Gamma$ 中是良类型的，当且仅当存在某种形式的 $\Gamma \vdash t: S$ 成立；否则，它在 $\Gamma$ 中是类型不正确的。

规则DM-VAR允许从环境中获取标识符$x$的类型方案。它同样适用于程序变量、内存位置和常数。如果环境中$\Gamma$没有关于$x$的假设，那么该规则不适用。在这种情况下，表达式$x$在$\Gamma$中是类型错误的——你能证明吗？关于常数的假设通常收集在一个所谓的初始环境$\Gamma_{0}$中。这是在封闭程序类型检查下的环境，因此每个子表达式都是在$\Gamma_{0}$的扩展$\Gamma$下进行类型检查的。当然，$\Gamma_{0}$分配给常数的类型方案必须与它们的操作语义一致；我们稍后会更多讨论这个问题（第1.7节）。规则DM-ABS指定了如何检查$\lambda$抽象$\lambda$ z.t的类型。其前提要求函数体$t$在额外的假设下是类型正确的，这导致$t$中所有自由出现的$z$接收一个共同的类型$\mathrm{T}$。其结论形成了函数形式参数（即$\mathrm{T}$）和结果（即$\mathrm{T}^{\prime}$）的类型箭头类型$\mathrm{T} \rightarrow \mathrm{T}^{\prime}$。值得注意的是，这个规则总是用类型$\mathrm{T}$来增强环境——请记住，按照惯例，类型是类型方案的一个子集，但绝不使用非平凡的类型方案。DM-APP规定，函数应用类型是函数类型的值域，前提是函数类型的域对实际参数是有效的类型。DMLET与操作语义紧密对应：而操作语义中局部定义let $z=t_{1}$ in $t_{2}$是在评估$t_{2}$之前，通过将$z$绑定到$t_{1}$的值来增强运行时环境；DM-LET的效果是在类型检查$t_{2}$之前，通过将$z$绑定到$t_{1}$的类型方案来增强类型检查环境。DM-GEN通过普遍量化一个不在环境中自由出现的类型变量集合，将一个类型转换成类型方案；这个限制在下面的例子1.2.20中进行讨论。相反，DMINST将类型方案转换为其一个实例，可以任意选择。这两操作被称为泛化和实例化。类型方案的概念以及规则DM-GEN和DMINST是ML类型系统的特点：它们将它与简单类型的$\lambda$-演算区分开来。

1.2.20 示例：允许在环境中自由出现的类型变量进行泛化是不合理的。例如，考虑类型判断 $\mathbf{z}: \mathrm{X} \vdash \mathbf{z}$ : X (1)，根据DM-VAR规则，这是有效的。将无限制的DM-GEN版本应用于它，我们得到 $\mathrm{z}: \mathrm{X} \vdash \mathrm{z}: \forall \mathrm{X} . \mathrm{X}$ (2)，由此，根据DM-INST，z : X $\vdash$ z : Y (3)。通过DM-ABS和DM-GEN，我们接着有 $\varnothing \vdash \lambda z . z: \forall X Y . X \rightarrow Y$。换句话说，恒等函数的参数类型和结果类型不相关！然后，表达式 $(\lambda z . z) \hat{0} \hat{0}$，它简化为卡住的表达式 $\hat{0} \hat{0}$，具有类型方案 $\forall z . z$。因此，类型正确的程序可能会导致运行时错误：类型系统是不健全的。

发生了什么？很明显，判断（1）是正确的，仅仅是因为分配给z的类型在其假设和其右侧是相同的。由于同样的原因，判断（2）和（3）是错误的——前者可以写成 $z: X \vdash z: \forall Y . Y$。实际上，这样的判断违背了环境存在的根本目的，因为它们忽视了它们的假设。

通过只在右侧普遍量化 $\mathrm{x}$，我们打破了假设中$\mathrm{X}$出现之间的联系，这些出现保持自由状态，而右侧的出现则变为绑定状态。这只有在假设中实际上没有自由出现的$\mathrm{X}$时才是正确的。

ML类型系统的关键特性是DM-ABS只能将类型T引入环境，而不是类型方案。实际上，这允许规则的结论形成箭头类型T → T'。如果规则改为将假设z: S引入环境，那么其结论就必须形成S → T'，这并不是一个良好形成的类型。换句话说，这个限制是必要的，以保持类型与类型方案之间的分层。如果我们去掉这种分层，从而允许全称量词深入到类型的内部，我们将得到System F的隐式类型版本（TAPL第23章）。System F的类型推论是不可判定的（Wells, 1999），而ML类型系统的类型推论是可判定的，我们稍后会证明这一点，所以这个设计选择具有相当大的影响。

1.2.21 练习 [\star, 推荐]：在DM中为表达式 $\lambda z_{1}$ 建立一个类型推导，令 $z_{2}=z_{1}$ 在 $z_{2}$ 中。

1.2.22 练习 [$\star$, 推荐]：设 int 是一个签名 $\star$ 的零元类型构造器。设 $\Gamma_{0}$ 包含绑定 $\hat{+}:$ int $\rightarrow$ int $\rightarrow$ int 和 $\hat{k}:$ int，对于每个整数 $k$。你能找到以下有效类型判断的推导吗？这些判断在简单类型的 $\lambda$-演算中哪些是有效的，其中令 $z=t_{1}$ 在 $t_{2}$ 中是语法糖 $\left(\lambda z . t_{2}\right) t_{1}$ 吗？

$$
\begin{gathered}
\Gamma_{0} \vdash \lambda z . z: \operatorname{int} \rightarrow \operatorname{int} \\
\Gamma_{0} \vdash \lambda z . z: \forall x . x \rightarrow x \\
\Gamma_{0} \vdash \text { et } f=\lambda z . z \hat{+} \hat{1} \text { in } f \hat{2}: \operatorname{int} \\
\Gamma_{0} \vdash \text { let } f=\lambda z . z \text { inf } f \hat{2}: \operatorname{int}
\end{gathered}
$$

显示表达式 $\hat{1} \hat{2}$ 和 $\lambda f$.(f $f$ ) 在 $\Gamma_{0}$ 中类型不正确。这些表达式在更强大的类型系统中可能类型正确吗？

1.2.23 练习 [$[\star \star \star]$]：实际上，图1-3中显示的规则并不完全是Damas和Milner原始的规则。在（Damas和Milner，1982）中，泛化和实例化规则是：

$$
\begin{gather*}
\frac{\Gamma \vdash \mathrm{t}: \mathrm{S} \quad \mathrm{X} \notin f t v(\Gamma)}{\Gamma \vdash \mathrm{t}: \forall \mathrm{X} . \mathrm{S}}  \tag{DM-GEN'}\\
\frac{\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{X}} . \mathrm{T} \quad \overline{\mathrm{Y}} \# f t v(\forall \overline{\mathrm{X}} . \mathrm{T})}{\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{Y}} .[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}} \tag{DM-INST'}
\end{gather*}
$$

哪里 $\forall$ X.S 表示 $\forall X \bar{X}$.T 如果 $S$ 表示 $\forall \bar{X}$.T。证明 DM-GEN' 和 DM-INST' 的组合等价于 DM-GEN 和 DM-INST 的组合。

DM拥有许多良好的理论性质，这些性质具有实际意义。首先，在关于常量语义的适当假设下，关于它们在初始环境中接收的类型方案，以及在有副作用的情况下，通过对let结构语法稍加限制，可以证明类型系统是健全的：也就是说，类型正确（封闭）的程序不会出错。这一基本性质确保了类型检查器接受的程序可以在没有运行时检查的情况下编译。此外，可以证明存在一个算法，给定一个（封闭的）环境$\Gamma$和一个程序$t$，该算法可以判断$t$是否相对于$\Gamma$类型正确，如果正确，会产生一个主要类型方案$\mathrm{S}$。一个主要类型方案是这样的：（i）它是有效的，即$\Gamma \vdash \mathrm{t}: \mathrm{S}$成立；（ii）它是最一般的，即形式为$\Gamma \vdash t: S^{\prime}$的每个判断都可以从$\Gamma \vdash \mathrm{t}: \mathrm{S}$通过DM-InsT和DM-GEN推导出来。（为了简单起见，我们只在封闭环境$\Gamma$的情况下陈述了类型推断算法的性质；在一般情况下的规格说明稍显复杂。）这意味着类型推断是可决定的：编译器不需要表达式用类型注解。这也意味着，在固定环境$\Gamma$下，与表达式$t$相关的所有类型信息都可以用一个单一（主要的）类型方案来总结，这非常方便。

## Road map

在证明上述主张之前，我们首先通过转向基于约束的环境来推广我们的表述。必要的工具，即约束语言、其解释以及若干约束等价法则，在1.3节中介绍。在1.4节中，我们描述了标准的基于约束的类型系统 $\operatorname{HM}(X)$ （Odersky, Sulzmann, 和 Wehr, 1999a; Sulzmann, Müller, 和 Zenger, 1999; Sulzmann, 2000）。我们证明了，当约束由自由有限项之间的等式构成时，$\operatorname{HM}(X)$ 是 DM 的重新表述。在更强大的约束语言的存在下，$\operatorname{HM}(X)$ 是 DM 的扩展。在1.5节中，我们提出了对 $\operatorname{HM}(X)$ 的原始重新表述，称为 $\operatorname{PCB}(X)$，其独特之处在于利用类型方案引入和实例化约束。在1.6节中，我们展示了，由于这些约束形式提供的额外表现力，类型推断可以被视为约束生成和约束解决的组合，正如之前所承诺的。实际上，我们定义了一个约束生成器，并将其与 $\operatorname{PCB}(X)$ 关联起来。然后，在1.7节中，我们给出了一个类型安全定理。它是纯粹用约束来表述的，但是——得益于之前各节发展的结果——同样适用于 $\operatorname{PCB}(X), \operatorname{HM}(X)$ 和 DM。

在整个核心材料中，约束的语法和解释部分未作具体规定。因此，发展是相对于它们参数化的——因此名称中的未知数$X$，如$\operatorname{HM}(X)$和$\operatorname{PCB}(X)$。我们实际上描述了一个基于约束的类型系统家族，它们共享一个共同的约束生成器和共同的类型健全性证明。然而，约束求解不能独立于$X$：相反，一个高效求解器的设计严重依赖于约束的语法和解释。在1.8节中，我们考虑在约束由自由树模型中的方程组成的具体情况下进行约束求解，并在标准一阶统一算法之上定义一个约束求解器。

本章的其余部分涉及框架的扩展。在1.9节中，我们将解释如何通过包括数据结构、模式匹配和类型注释在内的一系列特性来扩展ML-计算 calculus。在1.10节中，我们将扩展约束语言，引入全称量化，并描述需要此扩展的一些额外特性，包括不同类型的类型注释、多态递归以及一等全称和存在类型。最后，在1.11节中，我们将通过行来扩展约束语言，并描述它们的应用，这些应用包括可扩展的变体和记录。

### 1.3 Constraints

在本节中，我们定义了约束的语法和逻辑含义。这两者都是部分未指定的。实际上，类型构造器集合（定义1.2.14）必须至少包含二元类型构造器 $\rightarrow$，但可能还包含更多。同样，约束的语法涉及一组所谓的类型上的谓词，我们要求它至少包含一个二元子类型谓词 $\leq$，但可能还包含更多。此外，类型构造器和谓词的逻辑解释几乎完全未指定。这种自由度使得不仅可以推理Damas和Milner的类型系统，还可以推理基于约束的一系列扩展系统。

除了 $\rightarrow$ 以外的类型构造符和除了 $\leq$ 以外的谓词永远不会在我们基于约束的类型系统的定义中明确出现，这是因为定义是关于它们参数化的。它们可以在（通常也是）初始环境 $\Gamma_{0}$ 分配给构造器和析构器的类型方案中出现。

子类型的引入对我们复杂性的影响很小。

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-020.jpg?height=566&width=1518&top_left_y=227&top_left_x=241)

图1-4：类型方案和约束的语法

证明，却又增加了框架的表达能力。当不希望使用子类型时，我们将谓词 $\leq$ 解释为等式。

## Syntax

我们现将约束类型方案的语法以及约束进行定义，并引入一些额外的约束形式作为语法糖。

1.3.1 定义：设$P$涵盖一个有限的或可枚举的谓词集合，其中每个谓词的签名形式为$\kappa_{1} \otimes \ldots \otimes \kappa_{n} \Rightarrow \cdot$，其中$n \geq 0$。设$\leq$是一个具有签名$\star \otimes \star \Rightarrow \bullet$的特殊谓词。

1.3.2 定义：类型方案和约束的语法在图14中给出，并受以下要求的进一步限制。在类型方案 $\forall \overline{\mathrm{X}}[C] . \mathrm{T}$ 和约束 $\mathrm{x} \preceq \mathrm{T}$ 中，类型 $\mathrm{T}$ 必须具有种类 $\star$。在约束 $P \mathrm{~T}_{1} \ldots \mathrm{T}_{n}$ 中，如果 $P$ 有签名 $\kappa_{1} \otimes \ldots \otimes \kappa_{n} \Rightarrow \cdot$，则类型 $\mathrm{T}_{1}, \ldots, \mathrm{T}_{n}$ 必须分别具有种类 $\kappa_{1}, \ldots, \kappa_{n}$。我们用 $\forall \overline{\mathrm{X}}$.T 表示 $\forall \overline{\mathrm{x}}[$ true].T，这允许将DM类型方案视为受限类型方案的一个子集。

我们用 $\mathrm{T}_{1} \leq \mathrm{T}_{2}$ 来表示二元谓词应用 $\leq \mathrm{T}_{1} \mathrm{~T}_{2}$，并将其称为子类型约束。按照惯例，$\exists$ 和 def 的绑定比 $\wedge$ 更紧；即，$\exists \overline{\mathrm{x}} . C \wedge D$ 等于 $(\exists \overline{\mathrm{x}} . C) \wedge D$，而 def $\mathrm{x}: \sigma$ in $C \wedge D$ 等于 $(\operatorname{def} \mathrm{x}: \sigma$ in $C) \wedge D$。在 $\forall \overline{\mathrm{x}}[C] . \mathrm{T}$ 中，类型变量 $\overline{\mathrm{X}}$ 在 $C$ 和 $\mathrm{T}$ 中绑定。在 $\exists \overline{\mathrm{X}}$. $C$ 中，类型变量 $\overline{\mathrm{X}}$ 在 $C$ 中绑定。类型方案 $\sigma$ 和约束 $C$ 的自由类型变量集合，分别记作 $f t v(\sigma)$ 和 $f t v(C)$，相应地定义。在 def $\mathrm{x}: \sigma$ in $C$ 中，标识符 $\mathrm{x}$ 在 $C$ 中绑定。类型方案 $\sigma$ 和约束 $C$ 的自由程序标识符集合，分别记作 $f p i(\sigma)$ 和 $f p i(C)$，也相应地定义。请注意，$\mathrm{x}$ 在约束 $\mathrm{x} \preceq \mathrm{T}$ 中是自由出现的。

我们立即引入一些派生的约束形式：

1.3.3 定义：令 $\sigma$ 为 $\forall \overline{\mathrm{X}}[C]$.T。如果 $\overline{\mathrm{X}} \# \operatorname{ftv}\left(\mathrm{T}^{\prime}\right)$ 成立，那么 $\sigma \preceq \mathrm{T}^{\prime}$（读作：$\mathrm{T}^{\prime}$ 是 $\sigma$ 的一个实例）表示约束 $\exists \overline{\mathrm{X}}$. $\left(C \wedge \mathrm{T} \leq \mathrm{T}^{\prime}\right)$。我们写 $\exists \sigma$（读作：$\sigma$ 有一个实例）为 $\exists \overline{\mathrm{x}} . C$，并让 $\mathrm{x}: \sigma$ 在 $C$ 中对于 $\exists \sigma \wedge \operatorname{def} \mathrm{x}: \sigma$ 在 $C$ 中。

受限类型方案推广了Damas和Milner的类型方案，而我们对于实例化约束的定义推广了Damas和Milner的实例关系（定义1.2.18）。让我们进行比较。首先，Damas和Milner的实例关系提供了一个“是/否”的答案，并且是纯语法的：例如，类型 $\mathrm{Y} \rightarrow \mathrm{Z}$ 不是 $\forall \mathrm{X}$. $\mathrm{X} \rightarrow \mathrm{X}$ 在Damas和Milner意义上的实例，因为 $\mathrm{Y}$ 和 $\mathrm{Z}$ 是不同的类型变量。而在我们的表述中，$\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X} \preceq \mathrm{Y} \rightarrow \mathrm{Z}$ 不是一个断言；而是一个约束，按照定义是 $\exists \mathrm{X}$. （真 $\wedge \mathrm{X} \rightarrow \mathrm{X} \leq \mathrm{Y} \rightarrow \mathrm{Z}$ ）。我们后面证明它与 $\exists \mathrm{X}$. $(\mathrm{Y} \leq \mathrm{X} \wedge \mathrm{X} \leq \mathrm{Z})$ 以及 $\mathrm{Y} \leq \mathrm{Z}$ 等价，或者，如果子类型被解释为等价，那么与 $\mathrm{Y}=\mathrm{Z}$ 等价。也就是说，$\sigma \preceq \mathrm{T}^{\prime}$ 表示了一个关于类型变量在 $f t v\left(\sigma, \mathrm{T}^{\prime}\right)$ 中的（表示的类型）的条件，以便 $\mathrm{T}^{\prime}$ 能够在逻辑上而非纯语法的意义上成为 $\sigma$ 的一个实例。第二，实例化约束的定义涉及子类型，以确保任何实例的 $\sigma$ 的超类型再次成为 $\sigma$ 的实例（参见图1-6中的C-ExTrans规则和引理1.3.17）。这与子类型的目的是一致的，即允许在预期超类型的地方提供子类型（TAPL第15章）。第三，也是最后一点，现在每个类型方案都带有一个约束。约束 $C$ ，其自由类型变量可能是也可能不是 $\overline{\mathrm{x}}$ 的成员，限制了类型方案 $\forall \overline{\mathrm{x}}[C]$.T的实例。这在实例化约束 $\exists \overline{\mathrm{X}}$. $\left(C \wedge \mathrm{T} \leq \mathrm{T}^{\prime}\right)$ 中表达，其中 $\overline{\mathrm{X}}$ 可能取的值受到 $C$ 必须满足的要求的限制。在DM类型方案中，这个要求消失了，因为 $C$ 是真的。我们的受限类型方案和实例化约束的概念是标准的：它们正是 $\operatorname{HM}(X)$ （Odersky，Sulzmann和Wehr，1999a）中定义的。

约束“true”，总是得到满足，主要用于指示不存在非平凡约束，而“false”，没有解决方案，可以理解为类型错误的指示。复合约束包括合取和存在量化，它们具有标准含义，以及类型方案引入和类型方案实例化约束，与Gustavsson和Svenningsson的约束抽象（2001b）相似。简而言之，在$C$中的构造def $\mathrm{x}: \sigma$将名字$\mathrm{x}$绑定到约束$C$内的类型方案$\sigma$。如果$C$包含形如$\mathrm{x} \preceq \mathrm{T}$的子约束，其中此出现的$\mathrm{x}$在$C$中是自由的，则此子约束获得含义$\sigma \preceq \mathrm{T}$。因此，约束$\mathrm{x} \preceq \mathrm{T}$确实是一个实例化约束，其中被实例化的类型方案通过名称引用。约束def $\mathrm{x}: \sigma$在$C$中可以看作是将类型方案$\sigma$显式替换为$C$中的名字x。稍后（第1.5节），我们使用这样的显式替换来替换类型环境。也就是说，在Damas和Milner的类型系统增强当前类型环境（DM-ABS，DM-LET）的地方，我们在当前约束中引入一个新的def绑定；在它查找当前类型环境（DM-VAR）的地方，我们使用实例化约束。关键是，然后由约束求解器选择减少显式替换的策略——例如，人们可能希望简化$\sigma$，然后再将其替换为$C$中的$\mathrm{x}$——而标准类型系统（如DM和$\mathrm{HM}(X)$）中的环境使用强制执行急切替换策略，这种策略效率低下，因此从未真正实现。类型方案引入和实例化约束的使用允许在不牺牲效率的情况下分离约束生成和约束求解，换句话说，就是没有在类型推断算法的描述和其实际实现之间引入差距。尽管我们计划描述的算法并不是新的，但其关于约束的描述是：据我们所知，我们def约束的唯一近亲可以在（Gustavsson和Svenningsson，2001b）中找到。Fähndrich、Rehof和Das的实例化约束（2000）也与之相关，但可能是递归的，并且旨在使用半合一程序求解，而不是扩展了创建和实例化类型方案功能的合一算法，就像我们这种情况。

在类型方案中引入约束的一个后果是，某些类型方案根本没有实例，或者只在某个特定约束成立时才有实例。例如，类型方案 $\sigma=\forall x[$ bool $=$ int].X$，其中零元类型构造子int和bool具有不同的解释，没有实例；也就是说，没有形式的约束 $\sigma \preceq \mathrm{T}^{\prime}$ 有解。类型方案 $\sigma=\forall \mathrm{Z}[\mathrm{X}=\mathrm{Y} \rightarrow \mathrm{Z}] . \mathrm{Z}$ 只有当 $\mathrm{X}=\mathrm{Y} \rightarrow \mathrm{Z}$ 对某些Z成立时才有实例；换句话说，对于每个 $\mathrm{T}^{\prime}$，$\sigma \preceq \mathrm{T}^{\prime}$ 蕴含着 $\exists \mathrm{Z}$. $(\mathrm{X}=\mathrm{Y} \rightarrow \mathrm{Z})$。（我们在第29页定义蕴涵。）我们后来证明，约束 $\exists \sigma$ 等价于 $\exists \mathrm{Z} . \sigma \preceq \mathrm{Z}$，其中 $\mathrm{Z} \notin f t v(\sigma)$ （练习1.3.23）。也就是说，$\exists \sigma$ 表达了要求 $\sigma$ 有实例的需求。没有实例的类型方案指示了类型错误，因此在许多情况下，人们希望避免它们；为此，我们经常使用约束形式 let $\mathrm{x}: \sigma$ in $C$，这要求 $\sigma$ 有实例，并同时将其与名称 $\mathrm{x}$ 相关联。由于def形式更为原始，它在低层次上更容易处理，但在1.3节之后不再显式使用；我们总是使用let。

1.3.4 定义：环境 $\Gamma$ 保持与定义1.2.19中一样，不同的是DM类型方案S被限制类型方案 $\sigma$ 替换。我们用 $d f p i(\Gamma)$ 表示 $d p i(\Gamma) \cup f p i(\Gamma)$。我们定义 $\varnothing$ 在 $C=C$ 中的 def 和 $\operatorname{def} \Gamma ; \mathrm{x}: \sigma$ 在 $C=$ def $\Gamma$ 在 def $\mathrm{x}: \sigma$ 中的 $C$。同样，我们定义 let $\varnothing$ 在 $C=C$ 和 let $\Gamma ; \mathrm{x}$ : $\sigma$ 在 $C=$ let $\Gamma$ 在 let $\mathrm{x}: \sigma$ 中的 $C$。我们定义 $\exists \varnothing=$ true 和 $\exists(\Gamma ; \mathrm{x}: \sigma)=$ $\exists \Gamma \wedge \operatorname{def} \Gamma$ 在 $\exists \sigma$ 中。

为了建立或表达约束之间的某些等价定律，我们需要约束上下文。上下文是一个带有零个、一个或多个孔的约束，写成[]. 上下文的语法如下：

$$
\mathcal{C}::=\square|C| \mathcal{C} \wedge \mathcal{C}|\exists \overline{\mathrm{x}} . \mathcal{C}| \operatorname{def} \mathrm{x}: \sigma \text { in } \mathcal{C} \mid \operatorname{def} \mathrm{x}: \forall \overline{\mathrm{x}}[\mathcal{C}] . \mathrm{T} \text { in } C
$$

约束上下文$\mathcal{C}$应用于约束$C$的方式通常定义，记作$\mathcal{C}[C]$。由于上下文可能有任意数量的孔洞，$C$在过程中可能会消失或被复制。由于孔洞可能出现在绑定器的范围内，$C$的一些自由类型变量和自由程序标识符在$\mathcal{C}[C]$中可能变为绑定。我们分别用$\operatorname{dtv}(\mathcal{C})$和$\operatorname{dpi}(\mathcal{C})$来表示$\mathcal{C}$可能捕获的类型变量集和程序标识符集。我们写let $\mathrm{x}: \forall \overline{\mathrm{x}}[\mathcal{C}] . T$在$C$中，代表$\exists \overline{\mathrm{x}} . \mathcal{C} \wedge \operatorname{def} \mathrm{x}: \forall \overline{\mathrm{x}}[\mathcal{C}] . T$在$C$中。能够表述这样的定义是我们需要多孔洞上下文的原因。我们让范围遍历存在性约束上下文，由$\mathcal{X}::=[] \mid \exists \overline{\mathrm{X}} . \mathcal{X}$定义。

## Meaning

我们已经定义了约束的语法并给出了它们含义的非正式描述。现在我们给出约束解释的正式定义。我们从模型定义开始：

1.3.5 定义：对于每种种类 $\kappa$，令 $\mathcal{M}_{\kappa}$ 是一个非空集合，其元素是种类 $\kappa$ 的基本类型。以下，$t$ 在 $\mathcal{M}_{\kappa}$ 中取值，对于某个可能从上下文中确定的 $\kappa$。对于每个类型构造器 $F$，其签名是 $K \Rightarrow \kappa$，令 $F$ 表示从 $\mathcal{M}_{K}$ 到 $\mathcal{M}_{\kappa}$ 的全函数，这里的索引积 $\mathcal{M}_{K}$ 是所有将域 $\operatorname{dom}(K)$ 映射到 $\mathcal{M}_{K(d)}$ 的元素的映射的集合。对于每个签名 $\kappa_{1} \otimes \ldots \otimes \kappa_{n} \Rightarrow \cdot$ 的谓词 $P$，令 $P$ 表示在 $\mathcal{M}_{\kappa_{1}} \times \ldots \times \mathcal{M}_{\kappa_{n}}$ 上的谓词。我们要求在 $\mathcal{M}_{\star} \times \mathcal{M}_{\star}$ 上的谓词 $\leq$ 是一个偏序关系。

为了方便起见，我们不严格使用符号，并用$F$表示类型构造器和其解释；对于谓词也同样处理。我们自由地假定在每个种类$\kappa$上都有一个二元等性谓词，其在$\mathcal{M}_{\kappa}$上的解释是等价性，因此，如果$\mathrm{T}_{1}$和$\mathrm{T}_{2}$具有种类$\kappa$，那么$\mathrm{T}_{1}=\mathrm{T}_{2}$是一个良构的约束。

通过改变类型构造器的集合、谓词的集合、地类型（ground types）的集合以及类型构造器和谓词的解释，可以定义一整个相关类型系统的家族。我们非正式地将这些选择的集合称为$X$。因此，在1.4节和1.5节中描述的类型系统$\operatorname{HM}(X)$和$\operatorname{PCB}(X)$，都是由$X$参数化的。

以下示例给出了定义地面类型集合以及类型构造符解释的标准方法。

1.3.6 示例[语法模型]：对于每种种类 $\kappa$，令 $\mathcal{M}_{\kappa}$ 由种类 $\kappa$ 的闭合类型组成。那么，基本类型是没有自由类型变量的类型，并构成了所谓的Herbrand宇宙。令每个类型构造器 $F$ 被解释为其自身。以这种方式定义基本类型并解释类型构造器的模型被称为语法的。

1.3.7 示例[树模型]：设路径π为方向的有穷序列。空路径记作ε，路径π和π'的连接记作π·π'。设树t为从路径到类型构造器的部分函数，其定义域非空且前缀封闭，且对于t定义域中的每条路径π，如果类型构造器t(π)的签名是K => κ，那么π·d属于t的定义域等价于d属于K的定义域，此外，对于每个d属于K的定义域，类型构造器t(π·d)的像种类为K(d)。如果π属于t的定义域，则以π为根的t的子树，记作t/π，是部分函数π'映射到t(π·π')。树是有限的当且仅当它具有有限定义域。树是规则的当且仅当它具有有限数量的不同子树。每个有限树因此都是规则的。设mathcal{M}_κ由那些t(ε)的像种类为κ的有限（分别地，规则）树t组成：那么，我们有一个有限（分别地，规则）的树模型。

如果$F$具有签名$K \Rightarrow \kappa$，可以将$F$解释为将$\mathcal{M}_{K}$中的$T$映射到由$t(\epsilon)=F$和对于$\operatorname{dom}(T)$中的$d$，$t / d=T(d)$定义的地基层类型$t \in \mathcal{M}_{\kappa}$的函数，即头部符号为$F$且以$d$为根的子树为$T(d)$的唯一地基层类型。然后，我们得到了一个自由树模型。请注意，自由的有限树模型与前面示例中定义的语法模型是一致的。

行（第1.11节）在树模型中解释，尽管不是自由模型。以下示例提出了不同的解释子类型谓词的方式。

1.3.8 示例 [等价性模型]：解释子类型谓词的最简单方式是让 $\leq$ 在每个 $\mathcal{M}_{\kappa}$ 上表示等价性。这样做 的模型被称为等价性模型。当除了等价性之外没有其他谓词可用时，我们称该模型仅为等价性模型。

1.3.9 示例[结构化，非结构化子类型]：设一个变化量$\nu$是集合$\{-,+\}$的一个非空子集，简写为-（逆变），+（协变）或$\pm$（不变）。定义两个变化量的组合作为一个结合交换运算，其中+是中性元素，且满足$--=+$和$\pm-= \pm \pm= \pm$。现在，考虑一个自由（有限或正则）树模型，其中每个方向$d$都附有一个固定的变化量$\nu(d)$。定义路径$\pi$的变化量$\nu(\pi)$为其元素变化量的组合。设$\leqslant$是类型构造器的偏序关系，使得（i）如果$F_{1} \leqslant F_{2}$成立，且$F_{1}$和$F_{2}$分别具有签名$K_{1} \Rightarrow \kappa_{1}$和$K_{2} \Rightarrow \kappa_{2}$，那么$K_{1}$和$K_{2}$在它们的域的交上相同，并且$\kappa_{1}$和$\kappa_{2}$相同；以及（ii）$F_{0} \leqslant F_{1} \leqslant F_{2}$意味着$\operatorname{dom}\left(F_{0}\right) \cap \operatorname{dom}\left(F_{2}\right) \subseteq \operatorname{dom}\left(F_{1}\right)$。设$\leqslant^{+}, \leqslant^{-}$，和$\leqslant^{\pm}$分别表示$\leqslant, \geqslant$和$=$。然后，以下定义子类型的解释：如果$t_{1}, t_{2} \in \mathcal{M}_{\kappa}$，那么仅当对于每个路径$\pi \in \operatorname{dom}\left(t_{1}\right) \cap \operatorname{dom}\left(t_{2}\right)$，$t_{1}(\pi) \leqslant^{\nu(\pi)} t_{2}(\pi)$成立时，才有$t_{1} \leq t_{2}$。不难验证$\leq$在每一个$\mathcal{M}_{\kappa}$上都是一个偏序关系。关于这种构造的更多细节，请参考（Kozen, Palsberg, 和 Schwartzbach., 1995）。以这种方式定义子类型的模型称为非结构化子类型模型。

通过让方向域和共域分别是逆变和协变，并除了类型构造器$\rightarrow$之外，引入两个具有签名$\star$的类型构造器$\perp$和$T$，可以得到一个简单的非结构子类型模型。这产生了一个模型，其中$\perp$是最小的基本类型，$T$是最大的基本类型，而箭头类型构造器在其域中是逆变的，在其共域中是协变的，一如往常。

非结构子类型的一个典型应用是在记录的类型系统中。例如，可以引入一个协变方向的内容种类 $\star$，一个种类 $\diamond$，一个类型构造器abs，其签名是 $\diamond$，一个类型构造器pre，其签名是 $\{$ 内容 $\mapsto \star\} \Rightarrow \diamond$，并且让 pre $\leqslant$ abs。这产生了一个模型，其中对于每个 $t \in \mathcal{M}_{\star}$，都有 pre $t \leq$ abs 成立。这种子类型称为非结构子类型，因为可比较的底层类型可能有不同的形状，比如 $\perp$ 和 $\perp \rightarrow \top$，或者 pre $T$ 和 abs。非结构子类型已经在（Kozen, Palsberg, 和 Schwartzbach., 1995; Palsberg, Wand, 和 O'Keefe, 1997; Pottier, 2001b; Niehren 和 Priesnitz, 2003）等文献中被研究。第1.11节更详细地介绍了记录上的类型检查操作。

当一个重要的特例出现时，任何两个通过$\leqslant$相关联的类型构造器具有相同的元数。在这种情况下，不难证明，任何通过子类型化相关联的两个地类型必须具有相同的形状，即如果$t_{1} \leq t_{2}$成立，那么$\operatorname{dom}\left(t_{1}\right)$和$\operatorname{dom}\left(t_{2}\right)$是相同的。因此，这种子类型的解释通常被称为原子子类型或结构子类型。它已经在有限（Mitchell, 1984, 1991b; Frey, 1997; Rehof, 1997; Kuncak和Rinard, 2003; Simonet, 2003）和正则（Tiuryn和Wand,）中进行了研究。

1993)案例。结构子类型通常用于自动程序分析中，这种分析通过添加原子注释来丰富标准类型，而不改变它们的形状。

我们的最后一个例子提出了除等价性和子类型之外的其他谓词。

1.3.10 示例[条件约束]：考虑一个非结构子类型模型。对于每个图像种类 $\kappa$ 的类型构造器 $F$ 和每个种类 $\kappa^{\prime}$，令 $(F \leqslant \cdot \Rightarrow \cdot \leq \cdot)$ 为具有签名 $\kappa \otimes \kappa^{\prime} \otimes \kappa^{\prime} \Rightarrow \cdot$ 的谓词。因此，如果 $\mathrm{T}_{0}$ 的种类是 $\kappa$ 并且 $\mathrm{T}_{1}, \mathrm{~T}_{2}$ 具有相同的种类，那么 $F \leqslant \mathrm{~T}_{0} \Rightarrow \mathrm{T}_{1} \leq \mathrm{T}_{2}$ 是一个良好形式的约束，称为条件子类型约束。其解释定义如下：如果 $t_{0} \in \mathcal{M}_{\kappa}$ 和 $t_{1}, t_{2} \in \mathcal{M}_{\kappa^{\prime}}$，那么当且仅当 $F \leqslant t_{0}(\epsilon)$ 时 $t_{1} \leq t_{2}$ 成立。换句话说，如果 $t_{0}$ 的头符号根据类型构造器的顺序超过 $F$，则子类型约束 $t_{1} \leq t_{2}$ 必须成立；否则，条件约束空缺成立。条件约束已在例如 (Reynolds, 1969a; Heintze, 1993; Aiken, Wimmers, 和 Lakshman, 1994; Pottier, 2000; Su 和 Aiken, 2001) 中被研究。

存在许多其他类型的约束；例如参见（Comon, 1993）。

在本章中，我们假设（除非另有说明）类型构造器集合、谓词集合以及模型，这些共同构成了参数$X$，是任意且固定的。

如同往常，一个约束的含义是其自由类型变量的含义的函数，这由一个具体赋值给出。如果需要，可以使用def前缀，将自由程序标识符的含义定义为约束的一部分，因此不必通过单独的赋值来给出。

1.3.11 定义：一个地面赋值 $\phi$ 是从 $\mathcal{V}$ 到 $\mathcal{M}$ 的一个总映射，保持种类不变。地面赋值通过 $\phi(F \mathrm{~T}_{1} \ldots \mathrm{T}_{n})= F(\phi(\mathrm{T}_{1}), \ldots, \phi(\mathrm{T}_{n}))$ 扩展到类型。然后，对于每种种类 $\kappa$ 的类型 $\mathrm{T}$，$\phi(\mathrm{T})$ 是种类 $\kappa$ 的一个地面类型。一个约束 $C$ 在地面赋值 $\phi$ 下是否成立，记作 $\phi \vdash C$（读作：$\phi$ 满足 $C$），由图1-5中的规则定义。一个约束 $C$ 是可满足的，当且仅当存在某个 $\phi$ 使得 $\phi \vdash C$ 成立。它是假的，当且仅当对于任何地面赋值 $\phi$ 和环境 $\Gamma$，都不成立 $\phi \vdash \operatorname{def} \Gamma$ 中的 $C$。

让我们现在解释定义约束满足的规则（图15）。它们是语法指导的：也就是说，对于一个给定的约束，最多只有一个规则适用。它由最大def前缀下出现的第一个构造的性质决定。CM-TRUE规则表明，形式为def $\Gamma$ in true的约束是一个重言式，即在任何赋值下都成立。没有规则匹配形式为def $\Gamma$ in false的约束，这意味着这样的约束没有解决方案。CM-PREDICATE规则指出含义

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-027.jpg?height=396&width=1502&top_left_y=228&top_left_x=239)

图1-5：约束的含义

谓词应用的意义由模型中谓词的解释给出。更具体地说，如果$P$的签名是$\kappa_{1} \otimes \ldots \otimes \kappa_{n} \Rightarrow \cdot$，那么，根据约束的良好形式，每个$\mathrm{T}_{i}$都是$\kappa_{i}$类型的，所以$\phi\left(\mathrm{T}_{i}\right)$是$\mathcal{M}_{\kappa_{i}}$中的地类型。根据定义1.3.5，$P$表示$\mathcal{M}_{\kappa_{1}} \times \ldots \times \mathcal{M}_{\kappa_{n}}$上的一个谓词，因此规则的的前提在数学上是良好形成的。它与$\Gamma$无关，这是很自然的，因为谓词应用没有自由程序标识符。CMAND要求每个连词在没有上下文的情况下都是有效的。$\Gamma$中的信息对每个分支都是可用的。CM-ExisTs允许类型变量$\overrightarrow{\mathrm{X}}$在$C$中表示任意地类型$\vec{t}$，与其通过$\phi$的映像无关。我们隐式地要求$\overrightarrow{\mathrm{X}}$和$\vec{t}$具有匹配的种类，以便$\phi[\overrightarrow{\mathrm{X}} \mapsto \vec{t}]$保持类型保存的地赋值。侧条件$\overline{\mathrm{x}} \# \mathrm{ftv}(\Gamma)$可以通过适当的$\alpha$-转换约束$\exists \overline{\mathrm{X}} . C$来满足，这防止了$\Gamma$中的类型变量$\overline{\mathrm{X}}$的自由出现受到不适当的影响。CM-INSTANCE涉及形如def $\Gamma$ in $\mathrm{x} \preceq \mathrm{T}^{\prime}$的约束。将约束$\mathrm{x} \preceq \mathrm{T}^{\prime}$转换为$\sigma \preceq \mathrm{T}^{\prime}$，其中，根据第二个前提，$\sigma$是$\Gamma(\mathrm{x})$。请回想一下，此类形式的约束在定义1.3.3中引入。环境$\Gamma$被替换为其本身的适当前缀，即$\Gamma_{1}$，以便$\sigma$的自由程序标识符保持其含义。

直观上很明显，约束 def x: σ 在 C 中和 [x ↦ σ] C 的含义是相同的，其中后者表示在 C 中将 σ 代入 x 的捕获避免替换。实际上，完全可以使用这种等价性作为 def 约束意义的定义，但当前的表述方式也很令人愉快。这证实了我们的（非正式）说法，即 def 形式是一种显式的替换形式。

约束可能既不满足也不为假。例如，考虑约束 $\exists \mathrm{Z} \cdot \mathrm{x} \preceq \mathrm{z}$。因为标识符 $\mathrm{x}$ 是自由的，CMINSTANCE 不适用，所以该约束不满足。此外，将其置于上下文 let $\mathrm{x}: \forall \mathrm{X} . \mathrm{X}$ in $\square$ 中，它通过每个地面赋值都成立，因此它也不为假。在这里，当 $f p i(C)=\varnothing$ 成立时，“$C$ 可满足”和“$C$ 为假”的断言是相反的，而在标准的一阶逻辑中，它们始终是相反的。

在形如 $\phi \vdash C$ 的判断中，底层赋值 $\phi$ 适用于 $C$ 的自由类型变量。以下陈述精确地描述了这一点。在第二个陈述中，$\circ$ 表示组合，而 $\theta(C)$ 是将捕获避免的类型替换 $\theta$ 应用于 $C$ 的结果。

1.3.12 引理：如果 $\overline{\mathrm{x}} \# \operatorname{ftv}(C)$ 成立，那么 $\phi \vdash C$ 和 $\phi[\overrightarrow{\mathrm{x}} \mapsto \vec{t}] \vdash C$ 是等价的。

1.3.13 引理：$\phi \circ \theta \vdash C$ 和 $\phi \vdash \theta(C)$ 是等价的。

## 带约束的推理

因为约束是我们处理ML类型系统核心，我们的大部分证明都涉及建立约束的逻辑性质，即蕴含或等价断言。让我们首先定义这些概念。

1.3.14 定义：我们写作 $C_{1} \Vdash C_{2}$，并且说 $C_{1}$蕴涵$C_{2}$，当且仅当，对于每一个赋值$\phi$以及每一个环境$\Gamma$，$\phi \vdash \operatorname{def} \Gamma$在$C_{1}$中意味着$\phi \vdash \operatorname{def} \Gamma$在$C_{2}$中也成立。我们写作$C_{1} \equiv C_{2}$，并且说$C_{1}$和$C_{2}$是等价的，当且仅当$C_{1} \Vdash C_{2}$和$C_{2} \Vdash C_{1}$同时成立。

这个定义通过满足它的二元组集合 $(\phi, \Gamma)$ 来衡量约束的强度，并且认为如果满足的这样的二元组越少，则约束越强。换句话说，当$C_{1}$对其自由类型变量和程序标识符施加比$C_{2}$更严格的要求时，$C_{1}$蕴含$C_{2}$。我们指出，当且仅当$C \equiv$假时，$C$是假的。容易验证蕴含关系是自反的、传递的，并且$\equiv$确实是一个等价关系。

我们立即利用约束等价的概念来定义类型构造器关于其一个参数是协变、逆变或不变的意义。设$F$是具有签名$\kappa_{1} \otimes \ldots \otimes \kappa_{n} \Rightarrow \kappa$的类型构造器。设$i \in\{1, \ldots, n\}$。$F$关于其第$i$个参数是协变（相应地，逆变，不变）当且仅当，对于所有适当种类的类型$\mathrm{T}_{1}, \ldots, \mathrm{T}_{n}$和$\mathrm{T}_{i}^{\prime}$，约束$F \mathrm{~T}_{1} \ldots \mathrm{T}_{i} \ldots \mathrm{T}_{n} \leq F \mathrm{~T}_{1} \ldots \mathrm{T}_{i}^{\prime} \ldots \mathrm{T}_{n}$等价于$\mathrm{T}_{i} \leq \mathrm{T}_{i}^{\prime}$（相应地，$\mathrm{T}_{i}^{\prime} \leq \mathrm{T}_{i}$，$\mathrm{~T}_{i}=\mathrm{T}_{i}^{\prime}$）。我们让读者验证以下事实：（i）在等式模型中，这三个概念是相同的；（ii）在无等式的树模型中，每个类型构造器关于其每个参数都是不变的；（iii）在非结构性的子类型模型中，如果方向$d$已被声明为协变（相应地，逆变，不变），那么包含$d$的每个类型构造器关于$d$是协变（相应地，逆变，不变）的。以下，我们要求类型构造器$\rightarrow$关于其域是逆变的，关于其陪域是协变的——这是具有子类型的类型系统中的标准要求（TAPL第15章）。这些性质被以下等价定律总结：

$$
\begin{equation*}
\mathrm{T}_{1} \rightarrow \mathrm{T}_{2} \leq \mathrm{T}_{1}^{\prime} \rightarrow \mathrm{T}_{2}^{\prime} \equiv \mathrm{T}_{1}^{\prime} \leq \mathrm{T}_{1} \wedge \mathrm{T}_{2} \leq \mathrm{T}_{2}^{\prime} \tag{C-ARrow}
\end{equation*}
$$

请注意，这是关于类型解释和子类型谓词的高级要求。例如，在无等式的树模型中，它总是得到满足。在非结构化子类型模型中，它归结为要求方向域和共域分别被声明为逆变和协变。在一般情况下，我们对模型没有任何了解，无法制定更精确的要求。因此，模型设计者有责任确保C-ARrow成立。

我们还利用约束等价的概念来定义两个类型构造器不兼容的含义。如果两个具有相同像类的类型构造器$F_{1}$和$F_{2}$对所有形式的约束$F_{1} \overrightarrow{\mathrm{T}}_{1} \leq F_{2} \overrightarrow{\mathrm{T}}_{2}$和$F_{2} \overrightarrow{\mathrm{T}}_{2} \leq F_{1} \overrightarrow{\mathrm{T}}_{1}$都是假的，则它们是不兼容的；在这种情况下，我们写作$F_{1} \bowtie F_{2}$。请注意，在一个无等号树模型中，任何两个不同的类型构造器都是不兼容的。在以下内容中，我们经常指出新引入的类型构造器必须是孤立的。我们隐式地要求，每当$F_{1}$和$F_{2}$中的每一个都是孤立的时候，$F_{1}$和$F_{2}$是不兼容的。因此，“孤立”的概念提供了一种简洁且模块化的方式来陈述一系列不兼容要求。我们认为类型构造器$\rightarrow$是孤立的。

蕴含性由任意约束上下文保持，如下定理所述。因此，约束等价是一种同余关系。在本章中，这些事实经常被隐含地使用。

1.3.15 定理 [同余]：$C_{1} \Vdash C_{2}$ 推出 $\mathcal{C}\left[C_{1}\right] \Vdash \mathcal{C}\left[C_{2}\right]$.

我们现将给出一系列提供有用蕴含法则的引理。

以下是存在量词的一个标准属性。

1.3.16 引理：$C \Vdash \exists \overline{\mathrm{x}}$. $C$.

以下引理表明，任何$\sigma$实例的超类型也是$\sigma$的一个实例。

1.3.17 引理：若 $\sigma \preceq \mathrm{T}$ 且 $\mathrm{T} \leq \mathrm{T}^{\prime}$，则 $\sigma \preceq \mathrm{T}^{\prime}$。

下一个引理给出了另一个有趣的简化法则。

1.3.18 引理：若 $\mathrm{X} \notin f t v(\mathrm{~T})$，则 $\exists \mathrm{X} .(\mathrm{X}=\mathrm{T})$ 成立。

以下引理指出，如果满足$D$，那么类型$\mathrm{T}$是受限类型方案$\forall \overline{\mathrm{x}}[D]$的一个实例。

1.3.19 引理：$D \Vdash \forall \overline{\mathrm{X}}[D] . \mathrm{T} \preceq \mathrm{T}$. 

（注意：由于数学符号在英文和中文中的通用性，上述翻译保留了原始的数学符号。）

这个技术性引理有助于证明下面定义1.3.21的正确性。

1.3.20 引理：设 $\mathrm{Z} \notin \operatorname{ftv}(C, \sigma, \mathrm{T})$。那么，$C \Vdash \sigma \preceq \mathrm{T}$ 成立当且仅当 $C \wedge \mathrm{T} \leq$ $\mathrm{Z} \Vdash \sigma \preceq \mathrm{Z}$ 成立。

定义类型方案$\sigma_{1}$比类型方案$\sigma_{2}$更通用是有用的。我们非正式的意图是让$\sigma_{1} \preceq \sigma_{2}$意味着：$\sigma_{2}$的每一个实例都是$\sigma_{1}$的实例。在定义1.3.3中，我们引入了约束形式$\sigma \preceq \mathrm{T}$作为语法糖。同样，人们可能希望将$\sigma_{1} \preceq \sigma_{2}$作为一个派生约束形式；然而，这是不可能的，因为在约束语言中没有通用量化也没有蕴含。然而，我们可以利用这些逻辑连接词在蕴含断言中是隐含的这一事实，通过定义一个形如$C \Vdash \sigma_{1} \preceq \sigma_{2}$的判断，其含义是：在约束$C$下，$\sigma_{1}$比$\sigma_{2}$更通用。

1.3.21 定义：我们写 $C \Vdash \sigma_{1} \preceq \sigma_{2}$ 当且仅当 $\mathrm{Z} \notin \operatorname{ftv}(C, \sigma_{1}, \sigma_{2})$ 时意味着 $C \wedge \sigma_{2} \preceq \mathrm{Z} \Vdash \sigma_{1} \preceq \mathrm{z}$。我们写 $C \Vdash \sigma_{1} \equiv \sigma_{2}$ 当 $C \Vdash \sigma_{1} \preceq \sigma_{2}$ 和 $C \Vdash \sigma_{2} \preceq \sigma_{1}$ 同时成立。

这种表示法并不含糊，因为断言 $C \Vdash \sigma \preceq \mathrm{T}$ 的含义最初由定义1.3.3和1.3.14给出，在新的定义下保留了相同的含义——这由上面的引理1.3.20所示。

下一个引理提供了一种利用定义1.3.21引入的类型方案之间的排序关系的方法。它指出，当一个类型方案位于def前缀内部时，它出现在逆变位置。换句话说，类型方案越通用，整个约束就越弱。

1.3.22 引理：如果 $C \Vdash \sigma_{1} \preceq \sigma_{2}$，那么 $C \wedge \operatorname{def} \mathrm{x}: \sigma_{2}$ 在 $D \Vdash \operatorname{def} \mathrm{x}: \sigma_{1}$ 中。

以下练习将这个结果推广到let形式。

1.3.23练习 $[\star \star, \nrightarrow]$ ：证明 $\mathrm{Z} \notin f t v(\sigma)$ 意味着 $\exists \sigma \equiv \exists \mathrm{Z} . \sigma \preceq \mathrm{Z}$。解释为什么，结果上，$C \Vdash \sigma_{1} \preceq \sigma_{2}$ 意味着 $C \wedge \exists \sigma_{2} \Vdash \exists \sigma_{1}$。利用这个事实证明 $C \Vdash \sigma_{1} \preceq \sigma_{2}$ 意味着 $C \wedge$ 让 x : $\sigma_{2}$ 在 $D \Vdash$ 让 $\mathrm{x}: \sigma_{1}$ 在 $D$。

下一个引理指出，在模等价的前提下，唯一不显式提及 $\mathrm{x}$ 却约束它的约束是假的。

1.3.24 引理：若 $C \Vdash \mathrm{x} \preceq \mathrm{T}$ 且 $\mathrm{x} \notin f p i(C)$，则意味着 $C \equiv$ 假。

以下引理表明，存在的全称量化符越多，类型方案的普遍性越强。

1.3.25 引理：令 $\mathrm{x}: \forall \overline{\mathrm{x}}[C_{1}]. \mathrm{T}$ 在 $C_{2} \Vdash$ 令 $\mathrm{x}: \forall \overline{\mathrm{x}} \overline{\mathrm{Y}}[C_{1}]. \mathrm{T}$ 在 $C_{2}$ 中。

相反，或许令人惊讶的是，有时可以从类型方案的普遍量化前缀中移除某些类型变量，而不损害其普遍性。这种情况发生在这些类型变量的值以一种唯一的方式确定时。简而言之，$C$ 决定 $\overline{\mathrm{Y}}$ 当且仅当，在给定 $f t v(C) \backslash \overline{\mathrm{Y}}$ 的值以及给定 $C$ 成立的情况下，可以以唯一的方式重建 $\bar{Y}$ 的值。

1.3.26 定义：当且仅当对于每个环境 $\Gamma$，在 $C$ 中满足 def $\Gamma$ 的两个地面赋值在 $\bar{Y}$ 外部相同时，它们也必须在 $\bar{Y}$ 上相同，此时 $C$ 确定的是 $\overline{\mathrm{Y}}$。

第82页的引理1.8.7给出了两个确定性实例，其中只有一个在自由树模型中有效。确定性在图1-6中的等价法则C-LETALL中被利用。

我们现将一组约束等价性法则的工具箱呈现出来。值得注意的是，它们并不构成约束等价性的完整公理化体系，实际上也不可能，因为约束的语法和含义部分未指定。

1.3.27 定理：图1-6中的所有等价律成立。

让我们解释一下。C-AND和C-ANDAnd规则表明连词是可交换和结合的。C-DuP规则指出可以自由地添加或删除冗余的连词，其中只有当一个连词被另一个连词所蕴含时，它才是冗余的。在本章中，这三个定律经常被隐含地使用。C-ExEx和C-Ex*允许将连续的存在量词分组并省略冗余的量词，其中只有当量词在其作用域内不是自由出现时，它才是冗余的。C-ExAnd允许连词和存在量词在不会发生捕获的情况下交换，这被称为作用域扩展定律。当这个规则从左到右定向时，其侧条件总是可以通过适当的α-转换来满足。C-ExTrans规则指出，对于类型$\mathrm{T}^{\prime}$来说，是$\sigma$的一个实例或者是一些$\sigma$实例的超类型是等价的。我们注意到，单型实例是它的超类型，即按照定义1.3.3，$\mathrm{T} \preceq \mathrm{T}^{\prime}$和$\mathrm{T} \leq \mathrm{T}^{\prime}$是等价的。因此，将C-ExTrans规则特化到$\sigma$是单型的情况，我们发现$\mathrm{T} \leq \mathrm{T}^{\prime}$等价于$\exists \mathrm{Z}$. $\left(\mathrm{T} \leq \mathrm{Z} \wedge \mathrm{Z} \leq \mathrm{T}^{\prime}\right.$)，对于新鲜的$\mathrm{Z}$，这是一个标准的等价定律。当从左到右定向时，它变成了一条有趣的简化定律：在子类型约束链中，可以省略像Z这样的中间变量，只要它是局部的，由存在量词$\exists \mathrm{Z}$作证。C-INID规则指出，在绑定$\mathrm{x}: \sigma$的作用域内，$\mathrm{x}$的每个自由出现都可以安全地替换为$\sigma$。对自由出现的限制源于侧条件$\mathrm{x} \notin d p i(\mathcal{C})$。当规则定向时，这个条件适用。

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

图1-6：约束等价法则
规则从左至右排列，其它的边界条件，即要求上下文中的let $\mathrm{x}: \sigma$在$\mathcal{C}$中不捕获$\sigma$的自由类型变量或自由程序标识符，可以通过适当的$\alpha$-转换始终得到满足。C-IN*通过允许简化多余的let绑定来补充前面的规则。我们注意到C-INID和C-IN*为消除let形式提供了一个简单的过程。C-INAND指出let形式与合取（conjunction）可以交换；CINAND*详细说明了一个常见的特例。C-INEX指出它与世界量化（existential quantification）可以交换。当规则从左至右排列时，其边界条件可以通过适当的$\alpha$-转换始终得到满足。C-LETLET指出，只要let形式绑定不同的程序标识符，并且在过程中没有捕获自由程序标识符，let形式就可以交换。C-LETAnd允许将合取$C_{1}$移到普遍量化类型变量$\overline{\mathrm{X}}$之外的约束类型方案$\forall \overline{\mathrm{x}}\left[C_{1} \wedge C_{2}\right]$.T中，前提是它不涉及任何普遍量化的类型变量$\overline{\mathrm{X}}$。当从左至右排列时，该规则产生一个重要的简化法则：实际上，取$\forall \overline{\mathrm{X}}\left[C_{2}\right]$.T的实例比取$\forall \overline{\mathrm{x}}\left[C_{1} \wedge C_{2}\right]$.T的实例要便宜，因为后者涉及创建$C_{1}$的副本，而前者则不涉及。C-LETDUP允许将一系列let绑定推入一个约束类型方案中，前提是在此过程中没有发生捕获。它不作为一个简化法则使用，而是作为某些证明中的工具。C-LETEx指出，对于一组类型变量$\bar{Y}$而言，在约束类型方案内部或作为类型方案的普遍量化部分进行存在量化没有任何区别。实际上，在任一情况下，取类型方案的实例意味着产生一个$\bar{Y}$存在量化的约束。C-LETALL提供了引理1.3.25的一个受限的逆命题。一起，C-LETEx和C-LETALL在一些情况下允许将存在量化提升到let形式的左侧。

1.3.28 示例：如果没有条件 $\exists \overline{\mathrm{X}} . C_{1}$ 确定 $\bar{Y}$，那么 C-LetAll 将是无效的。例如，考虑约束 let $\mathrm{x}: \forall \mathrm{Y} . \mathrm{Y} \rightarrow \mathrm{Y}$ 在 $(\mathrm{x} \preceq$ int $\rightarrow$ int $\wedge \mathrm{x} \preceq$ bool $\rightarrow$ bool)$ (1)$ 中，其中 int 和 bool 是不兼容的零元类型构造器。通过 C-INID 和 C-IN*，它等价于 $\exists \mathrm{Y}$. $\mathrm{Y} \rightarrow$ $\mathrm{Y} \leq$ int $\rightarrow$ int $) \wedge \exists \mathrm{Y}$. $\mathrm{Y} \rightarrow \mathrm{Y} \leq$ bool $\rightarrow$ bool $)$，即真。现在，如果 C-LETALL 没有它的附带条件就是有效的，那么 (1) 也应等价于 $\exists \mathrm{Y}$.let $\mathrm{x}: \mathrm{Y} \rightarrow \mathrm{Y}$ 在 $(\mathrm{x} \preceq$ int $\rightarrow$ int $\wedge \mathrm{x} \preceq$ bool $\rightarrow$ bool)$ 中，通过 C-INID 和 C-IN* 这是 $\exists \mathrm{Y}$。(Y $\rightarrow \mathrm{Y} \leq$ int $\rightarrow$ int $\wedge \mathrm{Y} \rightarrow \mathrm{Y} \leq$ bool $\rightarrow$ bool)$。通过 C-ARROW 和 C-ExTrans，这是 int $=$ bool，即假。因此，在这种情况下该法则无效。很容易看出原因：当类型方案 $\sigma$ 包含一个 $\forall \mathrm{Y}$ 量词时，$\sigma$ 的每个实例都获得自己的 $\exists \mathrm{Y}$ 量词，使 Y 成为一个不同的（局部）类型变量；然而，当 $\mathrm{Y}$ 没有被普遍量化时，所有 $\sigma$ 的实例都共享对一个单一的（全局）类型变量 Y 的引用。这对应于这样的直觉：在前一种情况下，$\sigma$ 在 Y 上是多态的，而在后一种情况下，它在 Y 上是单态的。引理 1.3.25 表明，在没有其附带条件的情况下，C-LETALL 只是一个蕴含法则，而不是等价法则。同样，一般来说，将存在量词从 let 形式的左手边提取出来是无效的。为了看到这一点，可以研究（等价的）约束 let $\mathrm{x}: \forall \mathrm{X}[\exists \mathrm{Y} . \mathrm{X}=\mathrm{Y} \rightarrow \mathrm{Y}] . \mathrm{X}$ 在 $(\mathrm{x} \preceq$ int $\rightarrow$ int $\wedge \mathrm{x} \preceq$ bool $\rightarrow$ bool)$ 中。

当然，在上述例子中，边条件“true 确定Y”并不成立：根据定义1.3.26，它等价于“在Y之外相同的两个地面赋值必须在Y上也相同”，一旦$\mathcal{M}_{\star}$包含两个不同的元素，如这里的int和bool，这就变成错误的了。然而，有些情况下边条件是成立的。例如，我们后来证明了$\exists X . Y=$ int 确定Y；见引理1.8.7。因此，C-LETALL规则表明 let $\mathrm{x}: \forall \mathrm{XY}[\mathrm{Y}=$ int]. $\mathrm{Y} \rightarrow \mathrm{X}$ 在C中（1）等价于 $\exists \mathrm{Y}$.let $\mathrm{x}: \forall \mathrm{X}[\mathrm{Y}=\operatorname{int}] . \mathrm{Y} \rightarrow$ $\mathrm{X}$ 在C中（2），前提是$\mathrm{Y} \notin f t v(C)$。这个直观很简单：因为方程$\mathrm{Y}=$ int 强迫Y取值int，无论Y是否被普遍量化都没有区别。我们注意到，通过C-LETAND规则，（2）等价于 $\exists \mathrm{Y}$. $\mathrm{Y}=\operatorname{int} \wedge$ let $\mathrm{x}: \forall \mathrm{X} . \mathrm{Y} \rightarrow \mathrm{X}$ 在C中（3）。在一个高效的约束求解器中，在使用C-INID消除let形式之前将（1）简化为（3）是值得的，因为这样做可以省去在每个C中$\mathrm{x}$的自由出现处复制类型变量$\mathrm{Y}$和方程$\mathrm{Y}=$ int的需要。

C-LETSuB 是一个环境强化引理的类似物：大致来说，它表明，如果在一个假设 $\mathrm{x}$ 具有类型 $\mathrm{X}$ 的条件下约束成立，其中 $\mathrm{X}$ 是 $\mathrm{T}$ 的某个超类型，那么在假设 $\mathrm{x}$ 具有类型 $\mathrm{T}$ 的条件下约束也同样成立。最后三条规则处理等价谓词。$\mathrm{C}-\mathrm{EQ}$ 规定用等价物替换等价物是有效的；请注意没有附带条件。当从左到右定向时，C-NAME 允许引入新的名字 $\overrightarrow{\mathrm{X}}$ 用于类型 $\overrightarrow{\mathrm{T}}$。像往常一样，$\overrightarrow{\mathrm{X}}$ 代表一组不同的类型变量。当然，只有当定义不是循环的，即类型变量 $\overline{\mathrm{X}}$ 在项 $\overline{\mathrm{T}}$ 中没有自由出现时，这才是有意义的。当从右到左定向时，C-NAME 可以被视为简化法则：它允许消除已经确定了值的类型变量。C-NAMEEQ 是 $\mathrm{C}-\mathrm{EQ}$ 和 $\mathrm{C}-\mathrm{NAME}$ 的结合。它显示，将幂等代换应用于约束 $C$ 等同于将 $C$ 放入某个特定上下文中。这立即导致以下事实的证明：

1.3.29 引理：$C \Vdash D$ 意味着 $\theta(C) \Vdash \theta(D)$。

强调这一点很重要，因为可以使用方程式、连接词和存在量化来模拟类型替换的效果，所以在定义基于约束的类型系统时，永远不需要使用类型替换——反而可以完全用约束来表达每个概念。在本章中，我们遵循这一路线，仅在处理基于替换的历史表述的类型系统DM时使用类型替换。

到目前为止，我们考虑了将def视为一个原始的约束形式，并从def、联结和存在量化的角度定义了let形式。这种方法的目标是为了简化几个约束等价法则的证明。然而，在本章的剩余部分，我们将专门使用let形式，而不再使用def构造。因此，从这里开始，可以丢弃def，假装let是原始的。这种观点的变化为我们提供了几个额外的属性，将在接下来的两个引理中陈述。首先，每个包含假子约束的约束都必须是假的。其次，没有可满足的约束具有自由程序标识符。

1.3.30 引理：$\mathcal{C}[$ 假 $] \equiv$ 假。

1.3.31 引理：如果C是可满足的，那么$f p i(C)=\varnothing$。

## 在仅限等式的句法模型中进行约束推理

我们已经给出了一些等价定律，这些定律对于任何约束解释都是有效的，也就是说，在任何一个模型内部都适用。然而，一个重要的特殊情况是仅限于等式的句法模型。实际上，在那个特定的设置中，我们的基于约束的类型系统与DM紧密相关。简而言之，我们的目标是证明每个可满足的约束都有一个规范解的形式，展示这一概念与最一般合一器的一般概念相对应，并确立最一般合一器的一些技术特性。

因此，现在让我们假设约束在仅平等语法的模型中被解释。让我们进一步假设，对于每一种类型$\kappa$，（i）至少有两个图像类型为$\kappa$的类型构造器，以及（ii）对于每个图像类型为$\kappa$的类型构造器$F$，存在一个$t \in \mathcal{M}_{\kappa}$使得$t(\epsilon)=F$。我们将违反（i）或（ii）的模型称为退化模型；有人可能会认为这样的模型没什么兴趣。在证明引理1.3.32和1.3.39时使用了模型非退化的假设。

在这些新假设下，平等的解释与其语法是一致的：模型中成立的每一个等式实际上都是一个语法上的真理。反之，当然也适用于每一个模型。

1.3.32 引理：如果真 $\Vdash \mathrm{T}=\mathrm{T}^{\prime}$ 成立，那么 $\mathrm{T}$ 和 $\mathrm{T}^{\prime}$ 重合。

在语法模型中，基本类型是有限的树形结构。因此，像 $\mathrm{X}=$ int $\rightarrow \mathrm{X}$ 这样的循环等式是错误的。

1.3.33 引理：$\mathrm{X} \in f t v(\mathrm{~T})$ 且 $\mathrm{T} \notin \mathcal{V}$ 意味着 $(\mathrm{X}=\mathrm{T})$ 蕴含为假。

一个解的形式是由方程的联结组成的，其中左手边是不同类型的变量，这些变量不出现在右手边，可能还包含一些存在量词。我们的定义与Lassez、Maher和Marriott（1988年）的解形式以及Jouannaud和Kirchner（1991年）的树解形式完全相同，不同之处在于我们允许使用前缀存在量词，这是由我们更丰富的约束语言所必需的。Jouannaud和Kirchner还定义了$d a g$解形式，这种形式可能小到指数级别。因为我们仅为了证明目的而定义解形式，所以在这一点上无需考虑性能。第1.8节中提出的有效约束求解器实际上操作的是图而不是树。类型方案引入和实例化构造不能出现在解形式中；实际上，如果当前处理的约束没有自由程序标识符，它们可以被展开掉。因此，它们在约束语言中的存在对本文节中的结果没有影响。

1.3 .34 定义：一个解的形式是 $\exists \overline{\mathrm{Y}} .(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$，其中 $\overline{\mathrm{X}} \# \mathrm{ftv}(\overline{\mathrm{T}})$。

解决了的形式为推理约束提供了一种便捷方式，因为每个可满足的约束都等价于一个解决了的形式。换句话说，每个约束都等价于一个解决了的形式或假。这个性质由以下引理确立，其证明提供了一个简单但有效的过程，将一个约束重写为一个解决了的形式或假。

1.3.35 引理：设 $f p i(C)=\varnothing$。那么，$C$ 等价于解的形式或假。

证明：我们首先确立每个方程的连结都等价于一个已解形式或假。为此，我们将鲁宾逊统一算法（1971年）呈现为一个重写系统。该系统的不变量是操作形如 $\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}} ; C$ 的约束，其中 $\overline{\mathrm{X}} \# \operatorname{tv}(\overline{\mathrm{T}}, C)$；冒号被视为一个特殊的连结，或者是假的。我们根据交换性识别 $C$ 中的方程。系统定义如下：

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

上述不变量确实由重写系统保持是很容易检查的。让我们也检查一下约束等价是否也被保持。对于第一条规则，这是显而易见的。对于第二和第三条规则，这是由于我们假设了一个自由树模型；对于第四条规则，是 $\mathrm{C}-\mathrm{EQ}$ 的结果；对于最后一条规则，是引理1.3.33的后果。此外，该系统是终止的；这可以通过一个顺序来证明，其中假是最小的元素，而形如 $\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}} ; C$ 的约束按词典顺序排列，首先按在 $C$ 中自由出现的类型变量的数量，其次按 $C$ 的大小。最后，这个重写系统的范式必须是以下形式之一：$\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}$; 真，其中（根据不变量）$\overline{\mathrm{X}} \# \mathrm{ftv}(\overline{\mathrm{T}})$ —— 也就是说，是一个已解的形式，或者是假。

接下来，我们将证明当前引理在$C$由方程、合取和存在量词构成时成立。将C-ExAnd从左到右定向产生一个终止的重写系统，该系统保持约束等价性。$C$的正常形式必须是$\exists \overline{\mathrm{Y}}$。$C^{\prime}$，其中$C^{\prime}$是方程的合取。根据之前的结果，$C^{\prime}$等价于一个已解形式或假。由于已解形式由存在量词保持，且$\exists \bar{Y}$.假是假的，因此$C$也同理。

最后，我们在一般情况下建立结果。我们假设 $f p i(C)=\varnothing$ (1)。将C-INID和C-IN*从左到右定向产生一个保持约束等价的终止重写系统。$C$的正常形式$C^{\prime}$不能包含任何类型方案引入形式；根据（1），它也不能包含任何实例化形式。因此，$C^{\prime}$仅由等式、合取和存在量化构成。根据之前的结果，它等价于一个已解决的形式或假，这意味着$C$也是如此。

可以对已解决的形式施加进一步的限制。一个解形 $\exists \overline{\mathrm{Y}} .(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$ 是典范的当且仅当其自由类型变量正好是 $\overline{\mathrm{X}}$。以下定义以等价方式表述了这一点。

1.3.36 定义：一个规范解形式是形如 $\exists \overline{\mathrm{Y}}$. $(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$ 的约束，其中 $f t v(\overline{\mathrm{T}}) \subseteq \overline{\mathrm{Y}}$ 且 $\overline{\mathrm{X}} \# \overline{\mathrm{Y}}$。

1.3.37 引理：每个已解的形式都与一个规范已解形式等价。

很容易描述规范解形式的解：它们是替换$[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}]$的基本细化。

1.3.38 引理：如果地面赋值 $\phi$ 满足规范解形式 $\exists \overline{\mathrm{Y}}$. $(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$，那么当且仅当存在一个地面赋值 $\phi^{\prime}$ 使得 $\phi(\overrightarrow{\mathrm{X}})=\phi^{\prime}(\overrightarrow{\mathrm{T}})$。因此，每个规范解形式都是可满足的。

证明：设存在$\exists \overline{\mathrm{Y}}$。$(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$为一个典型解形式。根据CM-Exists和CMPredicate，$\phi$满足$\exists \overline{\mathrm{Y}}$。$(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$当且仅当存在$\vec{t}$使得$\phi[\overrightarrow{\mathrm{Y}} \mapsto$ $\vec{t}](\overrightarrow{\mathrm{X}})=\phi[\overrightarrow{\mathrm{Y}} \mapsto \vec{t}](\overrightarrow{\mathrm{T}})$。得益于假设$\overline{\mathrm{X}} \# \overline{\mathrm{Y}}$和$ftv(\overline{\mathrm{T}}) \subseteq \overline{\mathrm{Y}}$，这等价于存在一个地面赋值$\phi^{\prime}$使得$\phi(\overrightarrow{\vec{X}})=\phi^{\prime}(\overrightarrow{\mathrm{T}})$。

因此，对于每个地面赋值 $\phi^{\prime}$，$\phi^{\prime}\left[\overrightarrow{\mathrm{X}} \mapsto \phi^{\prime}(\overrightarrow{\mathrm{T}})\right]$ 满足 $\exists \overline{\mathrm{Y}}$. $(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$，这证明了这一约束是可满足的。

联合引理1.3.37和1.3.38表明，每个解的形式都是可满足的。我们对规范解形式的兴趣源于以下基本性质，它提供了规范解形式间蕴涵关系的语法刻画：如果从逻辑意义上说，$\exists \bar{Y}_{1} \cdot\left(\vec{X}=\vec{T}_{1}\right)$比$\exists \bar{Y}_{2} \cdot\left(\vec{X}=\vec{T}_{2}\right)$更具体，那么在语法意义上，$\vec{T}_{1}$细化了$\overrightarrow{\mathrm{T}}_{2}$。反之亦然（你能证明吗？），但这里不需要。

1.3.39 引理：如果存在 $\overline{\mathrm{Y}}_{1}$ 使得 $(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}_{1})$ 成立蕴含存在 $\overline{\mathrm{Y}}_{2}$ 使得 $(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}_{2})$ 成立，其中两边都是规范解形式，那么存在一个类型代换 $\varphi$ 使得 $\overrightarrow{\mathrm{T}}_{1}=\varphi(\overrightarrow{\mathrm{T}}_{2})$。

作为推论，我们发现，在固定它们的自由类型变量集合$\overline{\mathrm{X}}$的条件下，规范解形式在$\alpha$转换和$\mathrm{C}$-Ex*下是唯一的。

1.3.40 引理：如果规范解形式 $\exists \bar{Y}_{1} \cdot(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}_{1})$ 和 $\exists \overline{\mathrm{Y}}_{2} \cdot(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}_{2})$ 是等价的，那么存在一个重命名 $\rho$ 使得 $\overrightarrow{\mathrm{T}}_{1}=\rho(\overrightarrow{\mathrm{T}}_{2})$。

请注意，规范解形式 $\exists \overline{\mathrm{Y}}_{1} \cdot(\overrightarrow{\mathrm{X}}_{1}=\overrightarrow{\mathrm{T}}_{1})$ 和 $\exists \overline{\mathrm{Y}}_{2} \cdot(\overrightarrow{\mathrm{X}}_{2}=\overrightarrow{\mathrm{T}}_{2})$ 的等价性并不意味着 $\overline{\mathrm{X}}_{1}$ 和 $\overline{\mathrm{X}}_{2}$ 相同。例如，考虑规范解形式真和 $\exists \mathrm{Y} .(\mathrm{X}=\mathrm{Y})$，根据 C-NAMEEQ，它们是等价的。人们可能希望进一步限制规范解形式，要求 $\overline{\mathrm{X}}$ 是约束 $\exists \overline{\mathrm{Y}} .(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$ 的基本类型变量的集合，即出现在所有等价约束中的自由类型变量的集合。然而，就我们的技术发展而言，似乎不这样做更为方便。相反，我们证明了在需要时可以明确地限制或扩展 $\overline{\mathrm{X}}$（引理1.3.43）。

以下定义允许以双重视角看待规范解形式，既可以视为约束，也可以视为幂等类型替换。后者在统一性处理的标准方法（Lassez、Maher 和 Marriott，1988；Jouannaud 和 Kirchner，1991）和 ML 类型系统的经典介绍中较为常见。

1.3.41 定义：如果 $[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}]$ 是域 $\overline{\mathrm{X}}$ 的幂等代换，那么让 $\exists[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}]$ 表示典范解形式 $\exists \overline{\mathrm{Y}} .(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$，其中 $\overline{\mathrm{Y}}=\operatorname{ftv}(\overline{\mathrm{T}})$。幂等代换 $\theta$ 是约束 $C$ 的最一般合一者，当且仅当 $\exists \theta$ 和 $C$ 是等价的。

按定义，等价的约束承认相同的最一般统一器。许多规范解决形式的性质可以用最一般统一器的术语来重新表述。根据引理1.3.31、1.3.35和1.3.37，每个可满足的约束都承认一个最一般统一器。根据引理1.3.40，如果 $\left[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}_{1}\right]$ 和 $\left[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}_{2}\right]$ 是$C$的最一般统一器，那么 $\overrightarrow{\mathrm{T}}_{1}$ 和 $\overrightarrow{\mathrm{T}}_{2}$ 在重命名的情况下是一致的。反之，如果 $[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}]$ 是$C$的最一般统一器，且如果 $\overline{\mathrm{X}} \# \rho$ 成立，那么 $[\overrightarrow{\mathrm{X}} \mapsto \rho \overrightarrow{\mathrm{T}}]$ 也是$C$的最一般统一器；实际上，这两个替换对应于$\alpha$-等价的规范解决形式。

以下结果将替换 $\theta$ 与规范解决形式 $\exists \theta$ 相关联，说明前者的每个地面细化都满足后者。

1.3.42 引理：$\theta(\存在 \theta) \equiv$ 真实。

以下引理提供了两个技术结果：最泛统一器$C$的定义域可以限制，使其成为$f t v(C)$的一个子集；它也可以扩展到包括任意新变量。下一个引理是一个简单的推论。

1.3.43 引理：设 $\theta$ 是 $C$ 的一个最一般合一者。如果 $\overline{\mathrm{Z}} \# f \operatorname{tv}(C)$，那么 $\theta \backslash \overline{\mathrm{z}}$ 也是 $C$ 的一个最一般合一者。如果 $\overline{\mathrm{z}} \# \theta$，那么存在一个扩展了 $\theta$ 的 $C$ 的最一般合一者，其定义域是 $\operatorname{dom}(\theta) \cup \overline{\mathrm{z}}$。

1.3.44 引理：设$\theta_{1}$和$\theta_{2}$是$C$的最一般合一者。令$\overline{\mathrm{x}}=\operatorname{dom}\left(\theta_{1}\right) \cap \operatorname{dom}\left(\theta_{2}\right)$。那么，$\theta_{1}(\overline{\mathrm{X}})$和$\theta_{2}(\overline{\mathrm{X}})$在重命名的情况下是一致的。

我们的最后一个技术结果将最一般的$C$统一项与最一般的$\exists$ X.C统一项相关联。它指出，前者是后者的扩展。此外，在某些新鲜度条件下，$\exists$ x. $C$的每一个最一般统一项都可以扩展为$C$的最一般统一项。

1.3.45 引理：如果 $\theta$ 是 $C$ 的最一般合一者，那么 $\theta \backslash \mathrm{X}$ 是 $\exists \mathrm{x} . C$ 的最一般合一者。反之，如果 $\theta$ 是 $\exists \mathrm{X} . C$ 的最一般合一者且 $\mathrm{x} \# \theta$ 以及 $f t v(\exists$ X.C $C) \operatorname{dom}(\theta)$，则存在一个类型代换 $\theta^{\prime}$ 使得 $\theta^{\prime}$ 扩展了 $\theta$，$\theta^{\prime}$ 是 $C$ 的最一般合一者，且 $\operatorname{dom}\left(\theta^{\prime}\right)=\operatorname{dom}(\theta) \cup \mathrm{X}$。

## 1.4 HM(X)

基于约束的类型系统出现在20世纪80年代（Mitchell, 1984; Fuh和Mishra, 1988），并在随后的十年里被广泛研究（Curtis, 1990; Aiken和Wimmers, 1993; Jones, 1994a; Smith, 1994; Palsberg, 1995; Trifonov和Smith, 1996; Fähndrich, 1999; Pottier, 2001b）。我们现在介绍这样一个系统，命名为$\operatorname{HM}(X)$，因为它是Hindley和Milner类型纪律的一个参数化扩展；参数$X$的含义在第24页解释。其原始描述归功于Odersky，Sulzmann和Wehr（1999a）。从那时起，它在一篇多篇工作中得到了完善（Sulzmann，Müller和Zenger, 1999; Sulzmann, 2000; Pottier, 2001a;）。

Skalka和Pottier，2002年）。这些演示每个都引入了较小的变化。在这里，我们遵循（Pottier，2001a），其本身受到（Sulzmann，Müller和Zenger，1999年）的启发。

## Definition

我们的 $\operatorname{HM}(X)$ 表示依赖于第1.3节中引入的约束语言。从技术上来说，我们处理约束的方法比（Odersky, Sulzmann, 和 Wehr, 1999a）更为直接。我们在一个模型内解释约束，给合取和存在量化赋予它们标准的意义，并推导出一系列等价定律（第1.3节）。另一方面，Odersky 等人并没有明确依赖于逻辑解释；相反，他们把约束等价公理化，也就是说，他们将一系列等价定律视为公理。因此，他们确保了高级证明，如类型安全和类型推断的正确性和完整性，独立于对约束的逻辑解释的低级细节。他们的方法更具普遍性，因为它允许处理其他的逻辑解释——例如“开放世界”解释，在这种解释中，约束不是在一个固定的模型内解释，而是在“当前”模型的扩展系列内解释。为了明确起见，在本章中我们避免了这一额外的抽象层次；然而，采用 Odersky 等人的方法所需的更改并不会很大，因为即将到来的证明确实主要依赖于约束等价定律，而不是约束的逻辑解释的低级细节。

我们的工作与Odersky等人的工作另一个轻微的不同之处在于，我们丰富了约束语言，引入了类型方案介绍和实例化形式，这在$\operatorname{HM}(X)$的最初表述中是没有的。为了防止这个添加影响到$\operatorname{HM}(X)$，我们要求在$\operatorname{HM}(X)$类型判断中出现的约束不能含有自由程序标识符。请注意，这并不阻止它们包含let形式；实际上，在建立$\operatorname{HM}(X)$与第1.5节中提出的类型系统之间的等价性时，我们将利用这个特性，其中新的约束形式被有效使用。

类型系统 $\operatorname{HM}(X)$ 由一个四元判断组成，其参数是一个约束 $C$，一个环境 $\Gamma$，一个表达式 $t$，以及一个类型方案 $\sigma$。一个判断写作 $C, \Gamma \vdash \mathrm{t}: \sigma$，其读法是：在假设 $C$ 和 $\Gamma$ 的条件下，表达式 $t$ 具有类型 $\sigma$。可以把 $C$ 看作是关于判断的自由类型变量的假设，而 $\Gamma$ 看作是关于 $t$ 的自由程序标识符的假设。请记住，$\Gamma$ 现在包含受约束的类型方案，并且 $\sigma$ 也是一个受约束的类型方案。

我们希望打字判断的有效性不是取决于

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-041.jpg?height=546&width=1516&top_left_y=227&top_left_x=237)

图1-7：$\operatorname{HM}(X)$ 的输入规则

语法，但仅限于其约束假设的意义。我们通过认为在约束假设等价的情况下，判断是相等的来强化这一观点。换句话说，类型判断 $C, \Gamma \vdash \mathrm{t}: \sigma$ 和 $D, \Gamma \vdash \mathrm{t}: \sigma$ 被认为是相同的，当 $C \equiv D$ 成立时。因此，分析判断的约束假设的语法是没有意义的。一个判断是有效的，或者成立，当且仅当它是通过图1-7中给出的规则可推导的。请注意，一个有效的判断可能涉及一个不可满足的约束。一个程序 t 在环境 $\Gamma$ 中是良好类型的，当且仅当存在某个可满足的约束 $C$ 使得形如 $C, \Gamma \vdash \mathrm{t}: \sigma$ 的判断成立。

让我们现在解释规则。与DM-VAR类似，HMX-VAR查找环境以确定与程序标识符$x$关联的类型方案。结论中出现的约束$C$必须足够强，以确保$\sigma$有一个实例；这是由第二个前提表达的。这个技术要求用于引理1.4.1的证明中。HMX-ABS、HMX-APP和HMX-LET分别与DM-ABS、DM-APP和DM-LET相同，不同之处在于假设$C$对每个子推导都是可用的。我们回忆一下，类型$\mathrm{T}$可以被视为类型方案$\forall \varnothing$ [真]。T（定义1.2.18和1.3.2）。因此，类型是类型方案的一个子集，这意味着$\Gamma ; z: \mathrm{T}$是一个良好形成的环境，$C, \Gamma \vdash \mathrm{t}: \mathrm{T}$是一个良好形成的类型判断。为了理解HMX-GEN，最好先考虑$C$为真的特殊情况。这产生了以下更简单的规则：

$$
\begin{equation*}
\frac{D, \Gamma \vdash \mathrm{t}: \mathrm{T} \quad \overline{\mathrm{x}} \# f t v(\Gamma)}{\exists \overline{\mathrm{x}} \cdot D, \Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{X}}[D] . \mathrm{T}} \tag{HMX-GEN'}
\end{equation*}
$$

第二个前提与DM-GEN相同：被泛化的类型变量不能在环境中自由出现。结论形成类型方案 $\forall \overline{\mathrm{X}}[D]$.T，其中类型变量$\overline{\mathrm{X}}$已经普遍量化，但仍然受到约束$D$的限制。请注意，在$D$中自由出现的类型变量可能不仅包括$\overline{\mathrm{X}}$，还包括在$\Gamma$中通常自由的其他类型变量。规则的结论带有约束$\exists \overline{\mathrm{X}} . D$，从而记录了新形成的类型方案应该有一个实例的要求；这同样用于引理1.4.1的证明中。HMX-GEN可以被视为HMX-GEN'的一个更宽松版本，其中当前约束的一部分，即$C$，如果它不关心正在泛化的类型变量，即$\overline{\mathrm{X}}$，则不需要复制。这种优化在实践中很重要，因为$C$可能非常大。其正确性的直观解释由约束等价法则$\mathrm{C}$ LETAND给出，该法则以let约束的术语表达了相同的优化。因为$\operatorname{HM}(X)$不使用let约束，所以优化被硬编码到类型规则中。HMX-INST允许取类型方案的实例。读者可能会惊讶地发现，与DM-INST相反，它并不涉及类型替换。相反，规则只是去掉普遍量化符，这等同于应用恒等替换$\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{X}}$。然而，应该记住，类型方案被认为在$\alpha$-转换下是相等的，因此在使用HMX-INST之前，可以重命名类型方案的普遍量化符。这样做足够表达力的原因在下面的定理1.4.7的证明中出现。类型方案携带的约束$D$作为HMX-INST结论中当前约束的一部分被记录下来。子类型规则HMX-SUB允许在任何时候用任意超类型$\mathrm{T}^{\prime}$替换类型$\mathrm{T}$。因为$\mathrm{T}$和$\mathrm{T}^{\prime}$都可能含有自由类型变量，所以$\mathrm{T} \leq \mathrm{T}^{\prime}$是否成立取决于当前假设$C$，这就是规则第二个前提是一个蕴含断言的原因。HMX-SUB的操作解释是，它要求所有子类型的使用都必须显式记录在当前约束中。请注意，即使将子类型解读为等价，HMX-SUB仍然是一个有用且必要的规则：然后，它允许利用在$C$中找到的类型方程。最后，HMXEXISTS允许在当前约束中出现的类型变量成为存在性量化。结果，这些类型变量不再在规则的结论中自由出现；换句话说，它们变成了以前提为根的子推导的局部变量。可以证明，类型系统中存在HMX-EXISTS不会增加良好类型程序集，但会增加有效类型判断集；这是一种令人愉快的技术便利。实际上，由于判断被认为在约束等价下是相等的，因此可以在任何时间透明地简化约束。（通过简化约束，我们的意思是将其替换为在句法表示上被认为更简单的等价约束。）考虑到这一点，发现规则HMX-Exists的一个效果是启用更多的简化：因为约束等价是一个同态，$C \equiv D$意味着$\exists \overline{\mathrm{X}} . C \equiv \exists \overline{\mathrm{X}} . D$，但反之通常不成立。例如，通常无法简化判断$\mathrm{X} \leq \mathrm{Y} \leq \mathrm{Z}, \Gamma \vdash \mathrm{t}: \sigma$，但如果已知$\mathrm{Y}$在$\Gamma$或$\sigma$中没有自由出现，那么HMX-EXISTS允许推导出$\exists \mathrm{Y} .(\mathrm{X} \leq \mathrm{Y} \leq \mathrm{Z}), \Gamma \vdash \mathrm{t}: \sigma$，这与$\mathrm{x} \leq \mathrm{Z}, \Gamma \vdash \mathrm{t}: \sigma$的判断相同。因此，已经启用了有趣的简化。请注意，$\mathrm{X} \leq \mathrm{Y} \leq \mathrm{Z} \equiv \mathrm{X} \leq \mathrm{Z}$不成立，而根据C-ExTRans，$\exists \mathrm{Y}$. $\mathrm{X} \leq \mathrm{Y} \leq \mathrm{Z}) \equiv \mathrm{X} \leq \mathrm{Z}$是成立的。

我们现将建立类型系统 $\operatorname{HM}(X)$ 的几个简单性质。我们的第一个引理是一个小的技术性质。

1.4.1 引理：如果 $C, \Gamma \vdash \mathrm{t}: \sigma$，那么 $C \Vdash \exists \sigma$。

下一个引理表明，加强判断的约束假设保持其有效性。换句话说，弱化判断保持其有效性。值得注意的是，在更依赖于类型替换的传统表述中，这一结果的类比是一个类型替换引理；例如参见（Tofte，1988，引理2.7），（Leroy，1992，命题1.2），（Skalka和Pottier，2002，引理3.4）。在这里，该引理进一步指出，弱化判断不会改变其推导的形状，在通过类型推导进行归纳推理时这是一个有用的性质。

1.4.2 引理[弱化]：如果 $C^{\prime} \Vdash C$，那么每个 $C, \Gamma \vdash \mathrm{t}: \sigma$ 的推导都可以转换成具有相同结构的 $C^{\prime}, \Gamma \vdash \mathrm{t}: \sigma$ 的推导。

证明：证明是对 $C, \Gamma \vdash \mathrm{t}: \sigma$ 的推导进行结构归纳。在每个证明情形中，我们采用图1-7中的记号。

- 情形HMX-VAR。该规则的结论是$C, \Gamma \vdash \mathrm{x}: \sigma$。它的前提是$\Gamma(\mathrm{x})=\sigma$（1）和$C \Vdash \exists \sigma$（2）。根据假设，我们有$C^{\prime} \Vdash C$（3）。通过蕴含的传递性，（3）和（2）意味着$C^{\prime} \Vdash \exists \sigma$（4）。根据HMX-VAR，（1）和（4）得出$C^{\prime}, \Gamma \vdash \mathrm{x}: \sigma$。
- 情形HMX-ABS、HMX-App、HMX-LET。根据归纳假设，分别根据HMX-ABS、HMX-APP或HMX-LET。
- 情形HMX-GEn。该规则的结论是$C \wedge \exists \overline{\mathrm{x}} . D, \Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{x}}[D]$.T。它的前提是$C \wedge D, \Gamma \vdash \mathrm{t}: \mathrm{T}$（1）和$\overline{\mathrm{x}} \# f t v(C, \Gamma)$（2）。根据假设，我们有$C^{\prime} \Vdash C \wedge \exists \overline{\mathrm{X}} . D$（3）。我们可以假设，不失一般性，$\overline{\mathrm{X}} \# \mathrm{ftv}\left(C^{\prime}\right)$（4）。将归纳假设应用于（1）和蕴含断言$C^{\prime} \wedge C \wedge D \Vdash C \wedge D$，我们得到$C^{\prime} \wedge C \wedge D, \Gamma \vdash \mathrm{t}: \mathrm{T}$（5）。通过将HMX-GEN应用于（5）、（2）和（4），我们得到$C^{\prime} \wedge C \wedge \exists \overline{\mathrm{x}} . D, \Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{x}}[D] . \mathrm{T}$（6）。根据（3）和C-Dup，约束$C^{\prime} \wedge C \wedge \exists \overline{\mathrm{x}} . D$和$C^{\prime}$是等价的，所以（6）是目标$C^{\prime}, \Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{x}}[D]$.T。
- 情形HmX-Inst。该规则的结论是$C \wedge D, \Gamma \vdash \mathrm{t}$ : T。它的前提是$C, \Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{X}}[D] . \mathrm{T}$（1）。根据假设，$C^{\prime}$蕴含$C \wedge D$（2）。因为（2）意味着$C^{\prime} \Vdash C$，归纳假设可以应用于（1），得出$C^{\prime}, \Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{x}}[D] . \mathrm{T}$（3）。通过HmX-Inst，我们得到$C^{\prime} \wedge D, \Gamma \vdash \mathrm{t}: \mathrm{T}$（4）。因为（2）意味着$C^{\prime} \equiv C^{\prime} \wedge D$，（4）是目标$C^{\prime}, \Gamma \vdash \mathrm{t}: \mathrm{T}$。
- 情形HmX-Sub。该规则的结论是$C, \Gamma \vdash \mathrm{t}: \mathrm{T}^{\prime}$。它的前提是$C, \Gamma \vdash \mathrm{t}: \mathrm{T}$（1）和$C \Vdash \mathrm{T} \leq \mathrm{T}^{\prime}$（2）。根据假设，我们有$C^{\prime} \Vdash C$（3）。将归纳假设应用于（1）和（3）得出$C^{\prime}, \Gamma \vdash \mathrm{t}: \mathrm{T}$（4）。通过蕴含的传递性，（3）和（2）意味着$C^{\prime} \Vdash \mathrm{T} \leq \mathrm{T}^{\prime}$（5）。根据HMX-SuB，（4）和（5）得出$C^{\prime}, \Gamma \vdash \mathrm{t}:

我们不直接为 $\operatorname{HM}(X)$ 提供类型健全性的证明。相反，在1.5节中，我们证明了它与另一个类型系统等价，后者本身后来被证明是健全的。基于语义定义的直接类型健全性结果可以在（Odersky, Sulzmann, 和 Wehr, 1999a）中找到。另一种遵循 Wright 和 Felleisen（1994b）句法方法的类型健全性证明出现在（Skalka 和 Pottier, 2002）中。最后，在（Pottier, 2001a）中提出了一种混合方法，该方法结合了前两种方法的一些优点。

## $\mathrm{HM}(\boldsymbol{X})$ 的另一种呈现方式

图1-7中给出的$\mathrm{HM}(X)$的呈现只有八条语法指导规则中的四条。它是类型系统的一个很好的规范，但远不是一个算法描述。作为朝向这种描述的第一步，我们提供了$\operatorname{HM}(X)$的另一种呈现，其中泛化只在let表达式中执行，而实例化只发生在对程序标识符的引用处（图1-8）。它的特点是所有判断都具有形式$C, \Gamma \vdash \mathrm{t}: \mathrm{T}$，而不是$C, \Gamma \vdash \mathrm{t}: \sigma$。以下定理说明这两种呈现实际上是等价的。

1.4.3 定理：如果且仅当 $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ 可以通过图1-8的规则推导出来，那么它是一个有效的 $\operatorname{HM}(X)$ 判断。

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-045.jpg?height=493&width=1502&top_left_y=233&top_left_x=239)

图1-8：$\mathbf{H M}(X)$ 的另一种表示方式

这个定理表明，图1-7和1-8的规则集导出相同的单态判断，即形式为 $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ 的相同判断。事实上，不能使用新的规则集推导出形式为 $C, \Gamma \vdash \mathrm{t}: \sigma$ 的判断，其中 $\sigma$ 不是一个单型，这只是一个技术上的简化，并没有深远的意义；下面前两个练习对这个议题提供了一些启示。

1.4.4 练习 $[**]$ ：证明这两个规则集导致相同的类型正确程序集合。

1.4.5练习[$\star \star$]：证明，如果将HMX-GEN添加到图18的规则集中，那么这两个规则集将得出完全相同的判断。

1.4.6 练习 $[\star \star \star, \nrightarrow]$ ：证明可以以类似的方式简化Damas和Milner的类型系统的呈现。即，为DM定义一组替代的类型规则，这组规则允许推导出形如 $\Gamma \vdash \mathrm{t}: \mathrm{T}$ 的判断；然后，证明这个新规则集与之前的规则集是等价的，如上所述。你的证明需要DM的哪些辅助性质？一个解决方案在（Clément, Despeyroux, Despeyroux, 和 Kahn, 1986）中给出。

## 将 $\mathrm{HM}(X)$ 与Damas和Milner的类型系统相关联

为了解释我们对$\operatorname{HM}(X)$的兴趣，我们希望展示它比Damas和Milner的类型系统更具普遍性。由于$\operatorname{HM}(X)$实际上是一系列类型系统的家族，我们必须使这个陈述更精确。首先，$\mathrm{HM}(X)$家族的每个成员都包含DM。相反，DM包含$\mathrm{HM}(=)$，这是通过将$\operatorname{HM}(X)$专门化为仅基于等式的语法模型设置而获得的基于约束的类型系统。

这些主张中的第一个很容易证明，因为从DM判断到$\operatorname{HM}(X)$判断的映射实质上是身份映射：在真实假设下，每个有效的DM判断都可以被视为有效的$\operatorname{HM}(X)$判断。这一说法依赖于这样一个事实，即DM类型方案$\forall \overline{\mathrm{X}}$。$\mathrm{T}$与受限类型方案$\forall \overline{\mathrm{X}}$ [true]。T相同，因此DM类型方案（相应地，环境）是$\operatorname{HM}(X)$类型方案（相应地，环境）的一个子集。其证明是例行的，除了可能在DM-INST的情况下，其中展示了在DM中应用替换的效果是如何通过在$\operatorname{HM}(X)$中加强当前约束来模拟的。

1.4.7 定理：如果在DM中成立 $\Gamma \vdash \mathrm{t}: \mathrm{S}$，那么在 $\operatorname{HM}(X)$ 中也成立 $\Gamma \vdash \mathrm{t}: \mathrm{S}$。

证明：证明是对 $\Gamma \vdash t: S$ 的推导进行结构归纳。在每个证明情形中，我们采用图1-3中的记号。

- 案例DM-VAR。规则的结论是 $\Gamma \vdash \mathrm{x}: \mathrm{S}$。其前提是 $\Gamma(\mathrm{x})=$ $\mathrm{S}$ (1)。根据定义和 $\mathrm{C}-\mathrm{Ex} *$，约束 $\exists \mathrm{S}$ 等价于真。将HMX-VAR应用于(1)和真 $\Vdash$ 真的断言，我们得到真，$\Gamma \vdash \mathrm{x}: \mathrm{S}$。
- 案例DM-ABS，DM-ApP，DM-LET。根据归纳假设以及分别对应的HMX-ABS，HMX-APP或HMX-LET。

情形DM-GEn。规则的结论是 $\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{x}}$.T。它的前提是 $\Gamma \vdash \mathrm{t}: \mathrm{T}(\mathbf{1})$ 和 $\overline{\mathrm{X}} \# \mathrm{ftv}(\Gamma)$ (2)。将归纳假设应用于(1)得到真，$\Gamma \vdash \mathrm{t}: \mathrm{T}$ (3)。此外，(2)意味着 $\overline{\mathrm{X}} \# \mathrm{ftv}(\mathrm{true}, \Gamma)$ (4)。根据HMX-GEN，(3)和(4)得出真，$\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{x}}[$ true].T。

- 案例Dm-Inst。规则的结论是 $\Gamma \vdash \mathrm{t}:[\overrightarrow{\mathrm{x}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$。它的前提是 $\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{X}} . \mathrm{T}$ (1)。我们可以假设，不失一般性，$\overline{\mathrm{X}} \# \mathrm{ftv}(\Gamma, \overline{\mathrm{T}})$ (2)。将归纳假设应用于(1)得到真，$\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{X}}[$ 真].T (3)。根据HMXInst，(3)意味着真，$\Gamma \vdash \mathrm{t}: \mathrm{T}$ (4)。根据引理1.4.2，我们可以弱化这个判断，以便得到 $\overrightarrow{\mathrm{x}}=\overrightarrow{\mathrm{T}}, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (5)。使用C-EQ，C-ExTrans和C-ExAnd，可以建立 $\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}} \Vdash \mathrm{T}=[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$ (6)。将HMX-SuB应用于(5)和(6)，我们得到 $\overrightarrow{\mathrm{x}}=\overrightarrow{\mathrm{T}}, \Gamma \vdash \mathrm{t}:[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$ (7)。最后，(2)意味着 $\overline{\mathrm{X}} \# f t v(\Gamma,[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T})$ (8)。将HMX-EXisTs应用于(7)和(8)，我们得到 $\exists \overline{\mathrm{X}} .(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}}), \Gamma \vdash \mathrm{t}:[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$ (9)。根据(2)和C-NAME，约束 $\exists \overline{\mathrm{X}} .(\overrightarrow{\mathrm{X}}=\overrightarrow{\mathrm{T}})$ 等价于真，所以(9)是目标。

我们目前感兴趣的是证明上面定义的$\mathrm{HM}(=)$包含在DM中。为此，我们必须将每个$\mathrm{HM}(=)$判断翻译成DM判断。很快就会发现，如果原始判断的约束假设是可以满足的，那么这是可能的。

我们首先解释如何将$\mathrm{HM}(=)$翻译成DM类型方案。这样的翻译之所以可能，是因为$\operatorname{HM}(=)$的定义假设了一个仅包含等式的语法模型。实际上，在这种设置中，每个可满足的约束都承认一个最一般的统一器（定义1.3.41），我们对其特性进行了充分利用。

事实上，我们不仅要翻译一个类型方案，还必须对其应用类型替换。不是将这两步分开进行，而是同时执行，并通过类型替换θ参数化翻译。（分开它们似乎并没有帮助。）θ下[σ]的定义有些复杂：它在本节以下引理的陈述中给出，该引理的证明确实证明了该定义是良好形成的。

1.4.8 引理：考虑一个类型方案 $\sigma$ 和一个幂等类型替换 $\theta$ ，使得 $f t v(\sigma) \subseteq \operatorname{dom}(\theta)$ （1）且 $\exists \theta \Vdash \exists \sigma$ （2）。记 $\sigma=\forall \overline{\mathrm{x}}[D]$.T，其中 $\overline{\mathrm{x}} \# \theta$ （3）。那么，存在一个类型替换 $\theta^{\prime}$ 使得 $\theta^{\prime}$ 扩展 $\theta$ ，$\operatorname{dom}\left(\theta^{\prime}\right)$ 是 $\operatorname{dom}(\theta) \cup \overline{\mathrm{X}}$ ，并且 $\theta^{\prime}$ 是 $\exists \theta \wedge D$ 的最一般统一器。设 $\overline{\mathrm{Y}}=f \operatorname{tv}\left(\theta^{\prime}(\overline{\mathrm{X}})\right) \backslash \operatorname{range}(\theta)$ 。那么， $\sigma$ 在 $\theta$ 下的翻译，记作 $\llbracket \sigma \rrbracket_{\theta}$ ，是 DM 类型方案 $\forall \overline{\mathrm{Y}} \cdot \theta^{\prime}(\mathrm{T})$ 。这是一个良好形成的定义。此外， $f t v\left(\llbracket \sigma \rrbracket_{\theta}\right) \subseteq \operatorname{range}(\theta)$ 成立。

证明：由（2），存在θ等价于存在θ且存在σ，这可以写成存在θ且存在X的补集.D。由（3）和C-ExAnd规则，这是存在X的补集。(θ且D)。因此，因为θ是存在θ的最一般合一者，θ也是存在X的补集的最一般合一者(θ且D)（4）。此外，ftv(存在X.(θ且D))是ftv(存在θ且存在σ)，根据存在θ的定义和（1），它是θ的域的子集（5）。由（4），（3），（5）和引理1.3.45，存在一个类型代换θ'，使得θ'扩展了θ（6），且θ'是存在θ且D的最一般合一者（7），且θ'的域是θ的域和X的补集的并集（8）。

让我们定义 $\overline{\mathrm{Y}}=f t v\left(\theta^{\prime}(\overline{\mathrm{X}})\right) \backslash \operatorname{range}(\theta)$ 和 $\llbracket \sigma \rrbracket_{\theta}=\forall \overline{\mathrm{Y}} \cdot \theta^{\prime}(\mathrm{T})$。根据(1)，我们有 $f t v(\mathrm{~T}) \subseteq \overline{\mathrm{X}} \cup \operatorname{dom}(\theta)$。应用 $\theta^{\prime}$ 并利用(6)，我们发现 $f t v\left(\theta^{\prime}(\mathrm{T})\right) \subseteq f t v\left(\theta^{\prime}(\overline{\mathrm{X}})\right) \cup \operatorname{range}(\theta)$，根据 $\overline{\mathrm{Y}}$ 的定义，可以写成 $f t v\left(\theta^{\prime}(\mathrm{T})\right) \subseteq \overline{\mathrm{Y}} \cup$ range $(\theta)$。两边减去 $\overline{\mathrm{Y}}$，我们发现 $\operatorname{ftv}\left(\llbracket \sigma \rrbracket_{\theta}\right) \subseteq \operatorname{range}(\theta) \mathbf{( 9 )}$。

为了证明$\llbracket \sigma \rrbracket_{\theta}$的定义是有效的，还需要证明它不依赖于$\overline{\mathrm{X}}$或$\theta^{\prime}$的选择。为了证明前者，只需建立$\overline{\mathrm{X}} \# \mathrm{ftv}\left(\llbracket \sigma \rrbracket_{\theta}\right)$，这实际上是由（3）和（9）得出的。至于后者，由于（6）、（7）和（8）施加的限制，以及引理1.3.44，不同的$\theta^{\prime}$选择可能只相差一个重命名$f t v\left(\theta^{\prime}(\overline{\mathrm{X}})\right) \backslash \operatorname{range}(\theta)$，即$\overline{\mathrm{Y}}$。因此，我们必须检查$\overline{\mathrm{Y}} \# \mathrm{ftv}\left(\llbracket \sigma \rrbracket_{\theta}\right)$，这根据定义是成立的。

请注意，如果 $\sigma$ 实际上是一个类型 $\mathrm{T}$，其中 $f t v(\mathrm{~T}) \subseteq \operatorname{dom}(\theta)$，那么 $\overline{\mathrm{X}}$ 是空的，所以 $\theta^{\prime}$ 是 $\theta, \overline{\mathrm{Y}}$ 是空的，并且 $\llbracket \mathrm{T} \rrbracket_{\theta}=\theta(\mathrm{T})$。换句话说，类型在 $\theta$ 下的翻译是通过 $\theta$ 的它的像。更一般地说，如下练习所陈述的，未受约束的类型方案（即约束为真的类型方案）的翻译是通过 $\theta$ 的它的像。

1.4.9 练习 $[\star \star, \nrightarrow]$: 证明当定义明确时，$\llbracket \forall \overline{\mathrm{X}} . \mathrm{T} \rrbracket_{\theta}$ 是 $\theta(\forall \overline{\mathrm{X}} . \mathrm{T})$。

当应用于非平凡的限制类型方案时，翻译就不仅仅是一种简单的类型替换。下面给出这种情况的一些例子。

1.4.10 示例：设 $\sigma=\forall \mathrm{XY}[\mathrm{X}=\mathrm{Y} \rightarrow \mathrm{Y}]$.X。设 $\theta$ 为恒等替换。类型模式 $\sigma$ 是闭合的，约束 $\exists \sigma$ 等价于真，因此 $\llbracket \sigma \rrbracket_{\theta}$ 是有定义的。我们必须找到一个类型替换 $\theta^{\prime}$，其域为 XY，且是最一般的 $X=Y \rightarrow Y$ 的统一者。所有这样的替换都是形式为 $[\mathrm{X} \mapsto(\mathrm{Z} \rightarrow \mathrm{Z}), \mathrm{Y} \mapsto \mathrm{Z}]$ 的，其中 $\mathrm{Z}$ 是新的。我们有 $f t v\left(\theta^{\prime}(\mathrm{XY})\right)=\mathrm{Z}$，从而 $\llbracket \sigma \rrbracket_{\theta}=\forall \mathrm{Z} . \mathrm{Z} \rightarrow \mathrm{Z}$。注意，选择 $\mathrm{Z}$ 并不重要，因为它在 $\llbracket \sigma \rrbracket_{\theta}$ 中是绑定变量。大致来说，翻译的效果是用在约束 $\mathrm{X}=\mathrm{Y} \rightarrow \mathrm{Y}$ 下的最一般解替换了受约束类型模式 $\mathrm{X}$ 的主体。

令 $\sigma=\forall \mathrm{XY}_{1}[\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}]$.X. 令 $\theta=[\mathrm{Y}_{2} \mapsto \mathrm{Z}_{2}]$. 我们有 $f t v(\sigma)=\mathrm{Y}_{2} \subseteq \operatorname{dom}(\theta)$. 约束 $\exists \sigma$ 等价于真，因此 $\llbracket \sigma \rrbracket_{\theta}$ 是有定义的。我们必须找到一个类型代换 $\theta^{\prime}$，其定义域为 $\mathrm{XY}_{1} \mathrm{Y}_{2}$，它扩展了 $\theta$ 并且是 $\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}$ 的最一般统一器。所有这样的代换都具有形式 $\left[\mathrm{X} \mapsto\left(\mathrm{Z}_{1} \rightarrow \mathrm{Z}_{2}\right), \mathrm{Y}_{1} \mapsto \mathrm{Z}_{1}, \mathrm{Y}_{2} \mapsto \mathrm{Z}_{2}\right]$，其中 $\mathrm{Z}_{1}$ 是新鲜的。我们有 $\operatorname{ftv}\left(\theta^{\prime}\left(\mathrm{XY}_{1}\right)\right) \backslash \operatorname{range}(\theta)=\mathrm{Z}_{1} \mathrm{Z}_{2} \backslash \mathrm{Z}_{2}=\mathrm{Z}_{1}$，从而 $\llbracket \sigma \rrbracket_{\theta}=\forall \mathrm{Z}_{1} \cdot \mathrm{Z}_{1} \rightarrow \mathrm{Z}_{2}$. 类型变量 $\mathrm{Z}_{2}$ 并没有全称量化——尽管它出现在 $\mathrm{X}$ 的象中，而 $\mathrm{X}$ 在 $\sigma$ 中是全称量化的——因为 $\mathrm{Z}_{2}$ 是 $\mathrm{Y}_{2}$ 的象，而 $\mathrm{Y}_{2}$ 在 $\sigma$ 中是自由的。

在攻击主要定理之前，让我们建立翻译的一些技术性质。首先，$\llbracket \sigma \rrbracket_{\theta}$ 对于 $\theta$ 在 $\operatorname{ftv}(\sigma)$ 外部的行为不敏感，这是一个自然性质，因为我们的非正式意图是让 $\theta$ 应用于 $\sigma$。

1.4.11 引理：如果 $\theta_{1}$ 和 $\theta_{2}$ 在 $f t v(\sigma)$ 上重合，那么 $\llbracket \sigma \rrbracket_{\theta_{1}}$ 和 $\llbracket \sigma \rrbracket_{\theta_{2}}$ 要么都未定义，要么都已定义且相同。

其次，如果$C \Vdash \sigma \preceq \mathrm{T}^{\prime}$成立，那么在$C$的最一般统一器下，$\sigma$和$\mathrm{T}^{\prime}$的翻译满足Damas和Milner的实例关系。可以大致说，实例关系在翻译过程中得到了保持。

1.4.12 引理：设 $f t v\left(\sigma, \mathrm{T}^{\prime}\right) \subseteq \operatorname{dom}(\theta)$ (1) 且 $\exists \theta \Vdash \exists \sigma$ (2)。设 $\exists \theta \Vdash \sigma \preceq \mathrm{T}^{\prime}$ (3)。那么，$\theta\left(\mathrm{T}^{\prime}\right)$ 是 DM 类型方案 $\llbracket \sigma \rrbracket_{\theta}$ 的一个实例。

证明：记 $\sigma=\forall \overline{\mathrm{X}}[D] . \mathrm{T}$，其中 $\overline{\mathrm{X}} \# \theta$ （4）和 $\overline{\mathrm{X}} \# f t v\left(\mathrm{~T}^{\prime}\right)$ （5）。由（1），（2）和（4），可以像引理1.4.8中所陈述的那样准确地定义 $\theta^{\prime}, \overline{\mathrm{Y}}$ 和 $\llbracket \sigma \rrbracket_{\theta}$。根据（5）和定义1.3.3，（3）与 $\exists \theta \Vdash \exists \overline{\mathrm{X}}$。（$D \wedge \mathrm{T}=\mathrm{T}^{\prime}$）是同义的。按照引理1.4.8的证明第一段的方式进行推理，我们发现存在一个类型代换 $\theta^{\prime \prime}$ 使得 $\theta^{\prime \prime}$ 扩展了 $\theta, \operatorname{dom}\left(\theta^{\prime \prime}\right)$ 是 $\operatorname{dom}(\theta) \cup \overline{\mathrm{X}}$，并且 $\theta^{\prime \prime}$ 是 $\exists \theta \wedge D \wedge \mathrm{T}=\mathrm{T}^{\prime}$ 的最一般统一器。

我们有 $\operatorname{dom}\left(\theta^{\prime}\right)=\operatorname{dom}\left(\theta^{\prime \prime}\right)(\mathbf{6})$。此外，$\theta^{\prime}$ 是 $\exists \theta \wedge D$ 的最一般统一项，而 $\theta^{\prime \prime}$ 是 $\exists \theta \wedge D \wedge \mathrm{T}=\mathrm{T}^{\prime}$ 的最一般统一项，这意味着 $\exists \theta^{\prime \prime} \Vdash \exists \theta^{\prime}(\mathbf{7})$。根据引理1.3.39，$\theta^{\prime \prime}$ 改进了 $\theta^{\prime}$。也就是说，存在一个类型代换 $\varphi$ 使得 $\theta^{\prime \prime}$ 是 $\varphi \circ \theta^{\prime}$ 限制在 $\operatorname{dom}(\theta) \cup \overline{\mathrm{x}}(\mathbf{8})$ 上的结果。我们可以要求 $\operatorname{dom}(\varphi) \subseteq \operatorname{range}(\theta) \cup f t v\left(\theta^{\prime}(\overline{\mathrm{X}})\right)(\mathbf{9})$ 而不损害（8）。

考虑 $\mathrm{X} \in \operatorname{dom}(\theta)$。因为 $\theta^{\prime \prime}$ 扩展了 $\theta$，我们有 $\theta^{\prime \prime}(\mathrm{X})=\theta(\mathrm{X})(\mathbf{1 0})$。此外，由（8），我们有 $\theta^{\prime \prime}(\mathrm{X})=\left(\varphi \circ \theta^{\prime}\right)(\mathrm{x})=(\varphi \circ \theta)(\mathrm{X})(\mathbf{1 1})$。使用（10）和（11），我们发现 $\theta(\mathrm{X})=\varphi(\theta(\mathrm{X}))$。因为这对于每个 $\mathrm{X} \in \operatorname{dom}(\theta)$ 都成立，所以 $\varphi$ 必须是范围 $(\theta)$ 上的恒等映射；即，$\operatorname{dom}(\varphi)$ \# 范围 $(\theta)$（12）成立。结合（9）和（12），我们发现 $\operatorname{dom}(\varphi) \subseteq f t v\left(\theta^{\prime}(\overline{\mathrm{X}})\right) \backslash \operatorname{range}(\theta)$，即 $\operatorname{dom}(\varphi) \subseteq \overline{\mathrm{Y}}(\mathbf{1 3})$。

通过构造 $\theta^{\prime \prime}$，我们得到 $\exists \theta^{\prime \prime} \Vdash \mathrm{T}=\mathrm{T}^{\prime}$。根据引理1.3.29，这意味着 $\theta^{\prime \prime}\left(\exists \theta^{\prime \prime}\right) \Vdash \theta^{\prime \prime}(\mathrm{T})=\theta^{\prime \prime}\left(\mathrm{T}^{\prime}\right)$，根据引理1.3.42，这可以理解为真 $\Vdash \theta^{\prime \prime}(\mathrm{T})=$ $\theta^{\prime \prime}\left(\mathrm{T}^{\prime}\right)$。根据引理1.3.32，$\theta^{\prime \prime}(\mathrm{T})$ 和 $\theta^{\prime \prime}\left(\mathrm{T}^{\prime}\right)$ 是一致的。因为根据（1）$f t v(\mathrm{~T})$ 是 $\operatorname{dom}(\theta) \cup \overline{\mathrm{X}}$ 的子集，并且根据（8），前者可以写作 $\varphi\left(\theta^{\prime}(\mathrm{T})\right)$。根据（1）并且因为 $\theta^{\prime \prime}$ 扩展了 $\theta$，后者是 $\theta\left(\mathrm{T}^{\prime}\right)$。因此，我们得到 $\varphi\left(\theta^{\prime}(\mathrm{T})\right)=\theta\left(\mathrm{T}^{\prime}\right)$。结合（13），这证明了 $\theta\left(\mathrm{T}^{\prime}\right)$ 是 $\forall \overline{\mathrm{Y}} . \theta^{\prime}(\mathrm{T})$ 的一个实例，即 $\llbracket \sigma \rrbracket_{\theta}$。

我们将翻译扩展到以下环境。$\llbracket \varnothing \rrbracket_{\theta}$ 是 $\varnothing$。如果 $\exists \theta \Vdash \exists \sigma$ 成立，那么 $\llbracket \Gamma ; \mathrm{x}: \sigma \rrbracket_{\theta}$ 是 $\llbracket \Gamma \rrbracket_{\theta} ; \mathrm{x}: \llbracket \sigma \rrbracket_{\theta}$，否则它是 $\llbracket \Gamma \rrbracket_{\theta}$。请注意，$\llbracket \Gamma \rrbracket_{\theta}$ 包含的绑定比 $\Gamma$ 少，这确保了当 $\exists \theta \Vdash \exists \sigma$ 不成立时，不会在翻译中使用绑定 $x: \sigma$。请记住，当 $f t v(\Gamma) \subseteq \operatorname{dom}(\theta)$ 成立时，$\llbracket \Gamma \rrbracket_{\theta}$ 是有定义的。

我们现在准备证明主要定理。请注意，通过要求 $\theta$ 是 $C$ 的一个最一般统一器，我们也要求 $C$ 是可满足的。带有不可满足约束的判断不能被翻译。

1.4.13 定理：设 $C, \Gamma \vdash \mathrm{t}: \sigma$ 在 $\operatorname{HM}(=)$ 中成立。设 $\theta$ 是 $C$ 的一个最一般合一器，使得 $f t v(\Gamma, \sigma) \subseteq \operatorname{dom}(\theta)$。那么，在 DM 中，$\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{t}: \llbracket \sigma \rrbracket_{\theta}$ 成立。

证明：首先，根据引理1.4.1，我们有 $C \Vdash \exists \sigma$。这可以写作 $\exists \theta \Vdash \exists \sigma$，这保证了 $\llbracket \sigma \rrbracket_{\theta}$ 是有定义的。证明是基于对 $\operatorname{HM}(=)$ 类型推导的结构归纳法。我们假设推导是用图1-8中的规则表达的，但为了可读性，将 HMDLETGEN 分裂为 HMX-LET 和 HMX-GEN。

- 情况HmD-VARInst。规则的结论是 $C \wedge D, \Gamma \vdash \mathrm{x}: \mathrm{T}$。根据假设，$\theta$ 是 $C \wedge D(\mathbf{1})$ 的最一般统一者，且 $\operatorname{ftv}(\mathrm{T}) \subseteq \operatorname{dom}(\theta)$ (2) 成立。规则的前提是 $\Gamma(\mathrm{x})=\sigma$ (3)，其中 $\sigma$ 代表 $\forall \overline{\mathrm{x}}[D]$.T。由 (1)，我们有 $\exists \theta \equiv C \wedge D \Vdash D \Vdash \exists \overline{\mathrm{x}} . D \equiv \exists \sigma$ (4)。此外，我们有 $f t v(\sigma) \subseteq f t v(\Gamma) \subseteq \operatorname{dom}(\theta)$ (5)。这些事实表明 $\llbracket \sigma \rrbracket_{\theta}$ 是定义良好的。结合 (3)，这意味着 $\llbracket \Gamma \rrbracket_{\theta}(\mathrm{x})=\llbracket \sigma \rrbracket_{\theta}$。根据DM-VAR，$\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{x}: \llbracket \sigma \rrbracket_{\theta}$ (6)。现在，根据引理1.3.19，我们有 $D \Vdash \sigma \preceq \mathrm{T}$，这结合 $\exists \theta \Vdash D$，得出 $\exists \theta \Vdash \sigma \preceq \mathrm{T}$ (7)。由 (7)，(4)，(5)，(2)，以及引理1.4.12，我们发现 $\theta(\mathrm{T})$ 是 $\llbracket \sigma \rrbracket_{\theta}$ 的一个实例。因此，将DM-INsT应用于 (6) 得出 $\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{t}: \theta(\mathrm{T})$。

- 情况HmD-ABs。规则的结论是 $C, \Gamma \vdash \lambda z . t: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$。其前提是 $C,(\Gamma ; \mathrm{z}: \mathrm{T}) \vdash \mathrm{t}: \mathrm{T}^{\prime}$。将其应用于归纳假设得出 $\llbracket \Gamma \rrbracket_{\theta} ; \mathrm{z}$ : $\theta(\mathrm{T}) \vdash \mathrm{t}: \theta\left(\mathrm{T}^{\prime}\right)$。根据DM-ABS，这意味着 $\llbracket \Gamma \rrbracket_{\theta} \vdash \lambda$ z.t $: \theta(\mathrm{T}) \rightarrow \theta\left(\mathrm{T}^{\prime}\right)$，即 $\llbracket \Gamma \rrbracket_{\theta} \vdash \lambda z . t: \theta\left(\mathrm{T} \rightarrow \mathrm{T}^{\prime}\right)$。

- 情况HMd-Apr。通过将 $\operatorname{dom}(\theta)$ 扩展到包括 $f t v(T)$，根据归纳假设，以及DM-APP。
- 情况HMX-Let。通过将 $\operatorname{dom}(\theta)$ 扩展到包括 $f t v(\sigma)$，根据归纳假设，以及DM-LET。
- 情况HmX-GEn。规则的结论是 $C \wedge \exists \sigma, \Gamma \vdash \mathrm{t}: \sigma$，其中 $\sigma$ 代表 $\forall \overline{\mathrm{X}}[D]$.T。根据假设，$\theta$ 是 $C \wedge \exists \sigma$ (1) 的最一般统一者，且 $f t v(\Gamma, \sigma) \subseteq \operatorname{dom}(\theta) \mathbf{( 2 )}$ 成立。规则的前提是 $C \wedge D, \Gamma \vdash \mathrm{t}: \mathrm{T}(\mathbf{3})$ 和 $\overline{\mathrm{X}} \# \mathrm{ftv}(C, \Gamma)$ (4)。我们可以进一步假设，不妨碍 $\overline{\mathrm{X}} \# \theta$ (5)。给定 (1)，(2)，和 (5)，我们可以像引理1.4.8中那样定义 $\theta^{\prime}$ 和 $\bar{Y}$。那么，$\theta^{\prime}$ 是 $\exists \theta \wedge D$ 的最

案例 HmD-Exists。规则的结论是 $\exists \overline{\mathrm{X}} . C, \Gamma \vdash \mathrm{t}$ ：T。根据假设，$\theta$ 是 $\exists \overline{\mathrm{X}} . C(\mathbf{1})$ 的最一般合一器，并且 (2) 中的 $f t v(\Gamma, \mathrm{T}) \subseteq \operatorname{dom}(\theta)$ 成立。规则的的前提是 $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ （3）以及 $\overline{\mathrm{X}} \# f t v(\Gamma, \mathrm{T})$。我们可以假设，不失一般性，$\overline{\mathrm{x}} \# \theta$ （4）。与之前的案例一样，我们可以扩展 $\theta$ 的定义域以保障 $\operatorname{ftv}(\exists \overline{\mathrm{X}} . C) \subseteq \operatorname{dom}(\theta)$ （5）。由 (1)，(4)，(5) 和引理 1.3.45，存在一个类型代换 $\theta^{\prime}$ 使得 $\theta^{\prime}$ 扩展 $\theta$ （6）且 $\theta^{\prime}$ 是 $C$ 的最一般合一器。将归纳假设应用于 $\theta^{\prime}$ 和 (3) 得到 $\llbracket \Gamma \rrbracket_{\theta^{\prime}} \vdash \mathrm{t}: \theta^{\prime}(\mathrm{T})$。由 (2)，(6) 和引理 1.4.11，这可以解读为 $\llbracket \Gamma \rrbracket_{\theta} \vdash \mathrm{t}: \theta(\mathrm{T})$。

定理1.4.7和1.4.13共同揭示了$\mathrm{DM}$与$\operatorname{HM}(=)$之间的精确对应关系：存在一种组合转换使二者相互转化。换句话说，它们可以被视为单一类型系统的两种等价表述。也可以说$\mathrm{HM}(=)$是基于约束的DM表述。此外，定理1.4.7指出，$\operatorname{HM}(X)$家族中的每个成员都是DM的扩展。这解释了我们对$\mathrm{HM}(X)$的双重兴趣，一方面作为$\mathrm{DM}$的一种替代表述，我们认为它更为愉悦，原因已经讨论过；另一方面作为一个更具表现力的框架。

### 1.5 一个纯粹基于约束的类型系统：$\operatorname{PCB}(X)$

在前一部分，我们提出了$\operatorname{HM}(X)$，这是Damas和Milner类型系统的一个优雅的基于约束的扩展。然而，正如那里所描述的，$\operatorname{HM}(X)$有一个缺点。一个类型判断涉及到一个约束，它代表对其自由类型变量的假设，以及一个环境，它代表对其自由程序标识符的假设。在let节点处，HMD-LETGEN将当前约束的一部分，即$D$，转换为一个类型方案，即$\forall \overline{\mathrm{x}}[D] . \mathrm{T}$，并将其存储到环境中。然后，在每次遇到let绑定变量的地方，HMD-VARINST从环境中检索这个类型方案，并将$D$的一个副本添加回当前约束中。实际上，在将类型方案$\forall \overline{\mathrm{X}}[D] . \mathrm{T}$存储在环境之前简化它是非常重要的，因为复制一个未简化的约束将是低效的。换句话说，为了保持效率，看起来约束生成和约束简化不能分开进行。

当然，在实际操作中，将这些阶段相互混合并不困难，所以问题不在于技术，而在于教学。实际上，我们之前就认为自然且可取地将它们分开。我们在第1.3节中引入了类型方案引入和消除约束，但在指定$\operatorname{HM}(X)$时并没有使用它们，目的是作为解决此问题的手段。在本节中，我们利用它们来给出$\mathrm{HM}(X)$的一种新颖表述，这种表述不再需要在环境和约束假设之间来回复制约束。实际上，环境是……（此处原文未提供后续内容）

| $\frac{C \Vdash \mathrm{x} \preceq \mathrm{T}}{C \vdash \mathrm{x}: \mathrm{T}}$ | $(\mathrm{VAR})$ | $\frac{C_{1} \vdash \mathrm{t}_{1}: \mathrm{T}_{1} \quad C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}_{2}}{\text { let } \mathrm{z}: \forall \mathcal{V}\left[C_{1}\right] \cdot \mathrm{T}_{1} \text { in } C_{2}}$ | (LET) |
| :---: | :---: | :---: | :---: |
| $\frac{C \vdash \mathrm{t}: \mathrm{T}^{\prime}}{}$ |  |  |  |
| $\frac{\text { let } \mathrm{z}=\mathrm{t}_{1} \text { in } \mathrm{t}_{2}: \mathrm{T}_{2}}{}$ |  |  |  |
| $\frac{C_{1} \vdash \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime} \quad C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}}{C_{1} \wedge C_{2} \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}}$ | $(\mathrm{APP})$ | $\frac{C \vdash \mathrm{t}: \mathrm{T}}{C \wedge \mathrm{T} \leq \mathrm{T}^{\prime} \vdash \mathrm{t}: \mathrm{T}^{\prime}}$ | (SUB) |
|  |  | $\frac{C \vdash \mathrm{t}: \mathrm{T} \quad \overline{\mathrm{x}} \# f t v(\mathrm{~T})}{\exists \overline{\mathrm{x}} \cdot C \vdash \mathrm{t}: \mathrm{T}}$ | (ExISTS) |

图1-9：$\operatorname{PCB}(X)$ 的键入规则

完全抑制：利用新的约束形式，我们在约束假设中编码有关程序标识符的信息。

## Presentation

我们现在使用完整的约束语言（第1.3节）。类型判断采用形式 $C \vdash \mathrm{t}$ : $\mathrm{T}$，其中 $C$ 可以有自由的类型变量和自由的程序标识符。允许导出此类判断的规则出现在图1-9中。与之前一样，我们根据约束等价性来识别判断。

让我们回顾一下规则。VAR规则表明，在任何意味着$x \preceq T$的约束下，$x$具有类型$T$。请注意，我们不再咨询环境中与$x$关联的类型方案——实际上，没有环境。相反，我们让约束假设记录下类型方案应该将$T$作为其一个实例的事实。因此，在判断$C \vdash t: T$中，通常程序标识符在$t$中自由出现也在$C$中自由出现。ABS要求$\lambda$-抽象的体$t$在假设$C$下具有类型$T'$。尽管在前提中没有关于$z$的明确假设，但$C$通常包含一些关于$z$的实例化约束，形式为$z \preceq T_i$。在规则的结论中，$C$被包裹在let前缀$z: T$ in $[$内，其中$T$是分配给$z$的类型。这有效地要求每个$T_i$表示$T$的超类型，正如所希望的。请注意，$z$在约束let $z: T$ in $C$中不自由出现，这是很自然的，因为它在$\lambda z.t$中也不自由出现。App与HMX-APP在风格上有轻微差异：其约束假设在其前提之间分割。不难证明，当弱化成立时（见下面的引理1.5.2），这个选择不会影响有效判断集。这种新的表述鼓励将图1-9的规则读作一个算法的规范，该算法给定$t$和$T$，产生$C$使得$C \vdash t: T$成立。在App的情况下，算法递归地对自己为每个子表达式调用，产生约束$C_1$和$C_2$，然后构建它们的联结。LET与ABS相似：通过将$C_2$包裹在let前缀中，它赋予了$C_2$中关于$z$的实例化约束意义。不同之处在于$z$现在可以分配一个类型方案，而不是单型。从描述$t_1$的约束$C_1$和类型$T_1$中最直接的方式构建一个适当的类型方案。在左侧前提中自由出现的所有类型变量都被泛化，因此记号$\forall \mathcal{V}[C_1]. T_1$是一个方便的简写，代表$\forall \operatorname{ftv}(C_1, T_1)[C_1]. T_1$。在$\mathrm{DM}$和$\operatorname{HM}(X)$中存在的“环境中自由出现的类型变量不得泛化”的附加条件自然消失了，因为判断不再涉及环境。SUB再次与HMX-SUB在风格上有轻微差异：上面关于App的评论同样适用于这里。EXISTS本质上与HMX-EXISTS相同。

在 $\operatorname{HM}(X)$ 的标准规范中，HMD-ABS 和 HMD-LET GEN 在环境中积累信息。通过环境，这些信息对 HMD-VARINST 可用，它检索并复制这些信息。然而在这里，没有明确传递任何信息。在程序标识符被绑定的地方，构建了一个类型方案引入约束；在程序标识符被使用的地方，产生了一个类型方案实例化约束。这两者仅通过我们对约束含义的定义相关联。

读者可能会对LET允许其左侧前提中出现的所有自由类型变量被泛化的事实感到困惑。以下练习有助于阐明这个问题。

1.5.1 练习 [ $\star$, 推荐]：为表达式 $\lambda z_{1}$ 建立类型推导。在 $\operatorname{PCB}(X)$ 中令 $z_{2}=z_{1}$，推导 $z_{2}$。与练习 1.2.21 的解法进行比较。

以下引理是引理1.4.2的一个类似物。

1.5.2 引理[弱化]：如果 $C^{\prime} \Vdash C$，那么每个 $C \vdash \mathrm{t}: \mathrm{T}$ 的推导都可以转换成具有相同结构的 $C^{\prime} \vdash \mathrm{t}: \mathrm{T}$ 的推导。

证明：证明是对推导 $C \vdash t: T$ 的结构归纳。在每个证明案例中，我们采用图1-9中的记法。

-情况VAR。由于蕴含的传递性。
-情况ABs。规则的结论是令 $\mathrm{z}: \mathrm{T}$ 在 $C \vdash \lambda$ z.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime}(\mathbf{1})$。根据假设，我们有 $C^{\prime} \Vdash$ 令 $\mathrm{z}: \mathrm{T}$ 在 $C$ (2)。我们可以假设，不失一般性，$\mathrm{z} \notin f p i\left(C^{\prime}\right)(\mathbf{3})$。规则的前提是 $C \vdash \mathrm{t}: \mathrm{T}^{\prime}(\mathbf{4})$。将归纳假设应用于(4)得到 $C \wedge C^{\prime} \vdash \mathrm{t}: \mathrm{T}^{\prime}$，根据ABs，这意味着令 $\mathrm{z}: \mathrm{T}$ 在 $(C \wedge$
$\left.C^{\prime}\right) \vdash \lambda$ z.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime} \mathbf{( 5 )}$。根据(3)和C-INAND*，令 $\mathrm{z}: \mathrm{T}$ 在 $\left(C \wedge C^{\prime}\right)$ 等价于 (令 $\mathrm{z}: \mathrm{T}$ 在 $C$ ) $\wedge C^{\prime}$，根据(2)和 $\mathrm{C}$-Dup，这等价于 $C^{\prime}$。因此，(5)是目标 $C^{\prime} \vdash \lambda z$.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$。
-情况APp。通过对每个前提应用归纳假设，使用 $C^{\prime} \Vdash C_{1} \wedge C_{2}$ 意味着 $C^{\prime} \Vdash C_{1}$ 和 $C^{\prime} \Vdash C_{2}$ 的事实。
-情况LET。与ABS情况类似。归纳假设仅应用于第二个前提。
-情况Sub。与Apr情况类似。
-情况ExISTs。参见Lemma 1.4.2证明中相应的情况。

## 关联 $\operatorname{PCB}(X)$ 与 $\operatorname{HM}(X)$

让我们现在为我们的主张提供证据，即 $\operatorname{PCB}(X)$ 是 $\operatorname{HM}(X)$ 的另一种表示形式。接下来的两个定理定义了从 $\operatorname{HM}(X)$ 到 $\operatorname{PCB}(X)$ 以及返回的有效转换。

第一个定理表明，如果在 $\operatorname{HM}(X)$ 中，在假设 $C$ 和 $\Gamma$ 下，$\mathrm{t}$ 具有类型 $\mathrm{T}$，那么在 $\operatorname{PCB}(X)$ 中，$\mathrm{t}$ 也在某些假设 $C^{\prime}$ 下具有类型 $\mathrm{T}$。关系 $C \Vdash$ 让 $\Gamma$ 在 $C^{\prime}$ 中表示 $C$ 包含通过将 $\Gamma$ 与 $C^{\prime}$ 对抗得到的剩余约束，$\Gamma$ 提供关于 $\mathrm{t}$ 中的自由程序标识符的信息，而 $C^{\prime}$ 包含关于这些程序标识符的具体化约束。该陈述要求 $C$ 和 $\Gamma$ 不含自由程序标识符，这是很自然的，因为它们是 $\operatorname{HM}(X)$ 判断的一部分。假设 $C \Vdash \exists \Gamma$ 排除了在 $C$ 中未明显出现的 $\Gamma$ 中含有约束的某种病态情况。当 $\Gamma$ 是初始环境时，这个假设消失；见定义 1.7.3。

1.5.3 定理：设 \( C \Vdash \exists \Gamma \)。假设 \( f p i(C, \Gamma)=\varnothing \)。如果 \( C, \Gamma \vdash \mathrm{t}: \mathrm{T} \) 在 \( \operatorname{HM}(X) \) 中成立，那么存在一个约束 \( C' \)，使得 \( C' \vdash \mathrm{t}: \mathrm{T} \) 在 \( \operatorname{PCB}(X) \) 中成立，并且 \( C \) 使得 \( \Gamma \) 在 \( C' \) 中被包含。

证明：证明是对推导 $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ 的结构归纳。在每个证明案例中，我们采用图1-8中的记法。

- 情况HmD-VarInst。规则的结论是 $C \wedge D, \Gamma \vdash \mathrm{x}: \mathrm{T}$。根据假设，我们有 $C \wedge D \Vdash \exists \Gamma$（1）以及 $f p i(C, D, \Gamma)=\varnothing$（2）。规则的前提是 $\Gamma(\mathrm{x})=\forall \overline{\mathrm{x}}[D] . \mathrm{T}$（3）。根据VAR，我们有 $\mathrm{x} \preceq \mathrm{T} \vdash \mathrm{x}: \mathrm{T}$，因此还需要证明 $C \wedge D \Vdash$ let $\Gamma$ in $\mathrm{x} \preceq \mathrm{T}$（4）。根据（3）、（2）和C-INID，约束let $\Gamma$ in $\mathrm{x} \preceq \mathrm{T}$等价于let $\Gamma$ in $\forall \overline{\mathrm{x}}[D]$. $\mathrm{T} \preceq \mathrm{T}$，根据（2）和C-IN*，这本身等价于 $\exists \Gamma \wedge \forall \overline{\mathrm{x}}[D] . \mathrm{T} \preceq \mathrm{T}$（5）。根据（1）和引理1.3.19，$C \wedge D$蕴含（5）。我们已经证明了（4）。

- 情况HmD-ABs。规则的结论是 $C, \Gamma \vdash \lambda z . \mathrm{t}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$。其前提是 $C,(\Gamma ; \mathbf{z}: \mathrm{T}) \vdash \mathrm{t}: \mathrm{T}^{\prime}(\mathbf{1})$。约束 $\exists \Gamma$ 和 $\exists(\Gamma ; \mathbf{z}: \mathrm{T})$ 是等价的，因此归纳假设适用于（1）并得到一个约束 $C^{\prime}$ 使得 $C^{\prime} \vdash \mathrm{t}: \mathrm{T}^{\prime}(\mathbf{2})$ 和 $C \Vdash$ let $\Gamma ; \mathrm{z}: \mathrm{T}$ in $C^{\prime}$（3）。将ABs应用于（2）得到let $\mathrm{z}: \mathrm{T}$ in $C^{\prime} \vdash \lambda$ z.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$。还需要验证 $C$ 蕴含 let $\Gamma$ in let $\mathrm{z}: \mathrm{T}$ in $C^{\prime}$ —这正是（3）。

- 情况HMD-App。规则的结论是 $C, \Gamma \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}$。其前提是 $C, \Gamma \vdash \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}(\mathbf{1})$ 和 $C, \Gamma \vdash \mathrm{t}_{2}: \mathrm{T}$（2）。将归纳假设应用于（1）和（2），我们得到约束 $C_{1}^{\prime}$ 和 $C_{2}^{\prime}$ 使得 $C_{1}^{\prime} \vdash$ $\mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}(\mathbf{3})$ 和 $C_{2}^{\prime} \vdash \mathrm{t}_{2}: \mathrm{T}(4)$ 和 $C \Vdash$ let $\Gamma$ in $C_{1}^{\prime}(\mathbf{5})$ 和 $C \Vdash$ let $\Gamma$ in $C_{2}^{\prime}(\mathbf{6})$。根据App，（3）和（4）意味着 $C_{1}^{\prime} \wedge C_{2}^{\prime} \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}$。此外，根据C-InAnd，（5）和（6）导致 $C \Vdash$ let $\Gamma$ in $C_{1}^{\prime} \wedge C_{2}^{\prime}$。

- 情况hmd-LetGen。规则的结论是 $C \wedge \exists \overline{\mathrm{x}} . D, \Gamma \vdash$ let $\mathrm{z}=$ $\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}_{2}$。根据假设

$\circ$ 案例HmD-Exists。规则的结论是 $\exists \overline{\mathrm{x}} . C, \Gamma \vdash \mathrm{t}: \mathrm{T}$。其前提是 $C, \Gamma \vdash \mathrm{t}: \mathrm{T}(\mathbf{1})$ 和 $\overline{\mathrm{x}} \# f t v(\Gamma, \mathrm{T})(\mathbf{2})$。根据假设，我们有 $\exists \overline{\mathrm{x}} . C \Vdash$ $\exists \Gamma$，根据引理1.3.16，这意味着 $C \Vdash \exists \Gamma$。因此，归纳假设适用于（1），并产生一个约束 $C^{\prime}$ 使得 $C^{\prime} \vdash \mathrm{t}: \mathrm{T}$（3）以及 $C \Vdash$ 让 $\Gamma$ 在 $C^{\prime}$ 中（4）。根据Exists，（3）和（2）意味着 $\exists \overline{\mathrm{x}} . C^{\prime} \vdash \mathrm{t}$ : T。还需要证明 $\exists \overline{\mathrm{X}} . C \Vdash$ 让 $\Gamma$ 在 $\exists \overline{\mathrm{x}} . C^{\prime}$ 中。根据蕴含的等价性，（4）意味着 $\exists \overline{\mathrm{X}} . C \Vdash \exists \overline{\mathrm{X}}$.let $\Gamma$ in $C^{\prime}$。结果遵循（2）和C-InEx。

第二个定理表明，如果在 $\operatorname{PCB}(X)$ 中，在假设 $C$ 下，$\mathrm{t}$ 具有类型 $\mathrm{T}$，那么在 $\operatorname{HM}(X)$ 中，在假设 $\Gamma$ 在 $C$ 中以及 $\Gamma$ 下，$\mathrm{t}$ 也具有类型 $\mathrm{T}$。这个想法很简单：约束 $C$ 表示关于初始判断的自由类型变量和自由程序标识符的联合假设。在 $\operatorname{HM}(X)$ 中，这两种假设必须分别保持。因此，我们将它们分解为一对环境 $\Gamma$ 和剩余约束 let $\Gamma$ in $C$，其中 $\Gamma$ 可以任意选择，只要它满足 $f p i(C) \subseteq d p i(\Gamma)$——即，只要它定义了所有相关的程序变量，而剩余的约束 let $\Gamma$ in $C$ 没有自由程序标识符，因此它只代表关于新判断类型变量的假设。不同的 $\Gamma$ 选择会导致不同的 $\operatorname{HM}(X)$ 判断，这些判断可能不可比较；这与ML类型系统没有主要类型（Jim，1995）的事实有关。同样，假设 $f p i(\Gamma)=f p i($ let $\Gamma$ in $C)=\varnothing$ 是很自然的，因为我们希望 $\Gamma$ 和 let $\Gamma$ in $C$ 出现在 $\operatorname{HM}(X)$ 判断中。

1.5.4 定理：假设 $f p i(\Gamma)=f p i($ 让 $\Gamma$ 在 $C)=\varnothing$ 且 $C \not \equiv$ 假。如果 $C \vdash \mathrm{t}: \mathrm{T}$ 在 $\operatorname{PCB}(X)$ 中成立，那么让 $\Gamma$ 在 $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ 在 $\operatorname{HM}(X)$ 中也成立。

证明：证明是基于对 $C \vdash \mathrm{t}: \mathrm{T}$ 的推导结构归纳的。在每一个证明情形中，我们采用图1-9的记号。

根据引理1.3.30，每次调用归纳假设时，前提条件 $C \not \equiv$ false 都会被保留。它只在情况VAR中明确使用，那里它保证手中的标识符在 $\Gamma$ 中是绑定的。

-情形VAR。规则的结论是 $C \vdash \mathrm{x}$ : T。它的前提是 $C \Vdash \mathrm{x} \preceq$ T (1)。根据引理1.3.24，(1)和假设 $C \not \equiv$ false意味着 $\mathrm{x} \in f p i(C)$。因为让 $\Gamma$ 在 $C$ 中没有自由程序标识符，这暗示着 $\mathrm{x} \in d p i(\Gamma)$，也就是说，环境 $\Gamma$ 必须定义 $\mathrm{x}$。设 $\Gamma(\mathrm{x})=\forall \overline{\mathrm{x}}[D] \cdot \mathrm{T}^{\prime}$ (2)，其中 $\overline{\mathrm{X}} \# \operatorname{ftv}(\Gamma, \mathrm{T})$ (3)。由(2)，HMD-VARInst，和HMD-SuB，我们得到 $D \wedge \mathrm{T}^{\prime} \leq$ $\mathrm{T},\Gamma \vdash \mathrm{x}: \mathrm{T}$。由(3)和HMD-ExisTs，这意味着 $\exists \overline{\mathrm{X}} .\left(D \wedge \mathrm{T}^{\prime} \leq \mathrm{T}\right), \Gamma \vdash \mathrm{x}: \mathrm{T}$ (4)。现在，由(3)，约束 $\exists \overline{\mathrm{X}} .\left(D \wedge \mathrm{T}^{\prime} \leq \mathrm{T}\right)$ 可以写成 $\forall \overline{\mathrm{X}}[D] . \mathrm{T}^{\prime} \preceq \mathrm{T}$ (5)。假设 $f p i(\Gamma)=\varnothing$ 暗示 $f p i(D)=\varnothing$ (6)。由(6)，C-InID和C$\mathrm{IN}^{*},(5)$ 等价于让 $\Gamma$ 在 $\mathrm{x} \preceq \mathrm{T}$ 中。因此，(4)可以写成让 $\Gamma$ 在 $\mathrm{x} \preceq$ $\mathrm{T}, \Gamma \vdash \mathrm{x}: \mathrm{T}$ 中。由(1)，根据蕴含的相等性，和引理1.4.2，这意味着让 $\Gamma$ 在 $C, \Gamma \vdash \mathrm{x}: \mathrm{T}$ 中。

-情形ABs。规则的结论是让 z : $\mathrm{T}$ 在 $C \vdash \lambda$ z.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$ 中。它的前提是 $C \vdash \mathrm{t}: \mathrm{T}^{\prime}$ (1)。设 $\Gamma^{\prime}$ 代表 $\Gamma ; \mathrm{z}: \mathrm{T}$。将归纳假设应用于(1)得到让 $\Gamma^{\prime}$ 在 $C, \Gamma^{\prime} \vdash \mathrm{t}: \mathrm{T}^{\prime}$ 中。由HMD-ABS，这意味着让 $\Gamma^{\prime}$ 在 $C, \Gamma \vdash \lambda z$.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$ 中。

-情形App。规则的结论是 $C_{1} \wedge C_{2} \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}$。它的前提是 $C_{1} \vdash \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$ 和 $C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}$。应用归纳假设分别得到让 $\Gamma$ 在 $C_{1}, \Gamma \vdash \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$ 和让 $\Gamma$ 在 $C_{2}, \Gamma \vdash \mathrm{t}_{2}: \mathrm{T}$ 中，这由引理1.4.2和HMD-APP暗示让 $\Gamma$ 在 $\left(C_{1} \wedge C_{2}\right), \Gamma \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}$ 中。

情形LET。规则的结论是令 $\mathrm{z}: \forall \mathcal{V}[C_{1}] \cdot \mathrm{T}_{1}$ 在 $C_{2} \vdash$ 令 $\mathrm{z}=$ $\mathrm{t}_{1}$ 在 $\mathrm{t}_{2}: \mathrm{T}_{2}$ 中。它的前提是 $C_{1} \vdash \mathrm{t}_{1}: \mathrm{T}_{1} (1)$ 和 $C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}_{2} (2)$。令 $\overline{\mathrm{X}}$ 代表 $f t v(C_{1}, \mathrm{~T}_{1})$。我们可以要求，不失一般性，$\overline{\mathrm{X}} \# f t v(\Gamma, C_{2})$ (3)。根据假设，我们有 $f p i(\Gamma)=\varnothing(4)$。我们还知道 $f p i($ 令 $\Gamma ; \mathbf{z}: \forall \mathcal{V}[C_{1}] . \mathrm{T}_{1}$ 在 $C_{2})=\varnothing$，这意味着 $f p i($ 令 $\Gamma$ 在 $C_{1})=\varnothing$。因此，归纳假设适用于 (1) 并得出令 $\Gamma$ 在 $C_{1}$ 中，$\Gamma \vdash \mathrm{t}_{1}: \mathrm{T}_{1}$ (5)。现在，令 $\sigma$ 代表 $\forall \overline{\mathrm{X}}($ 令 $\Gamma$ 在 $C_{1}] . \mathrm{T}_{1}$ 和 $\Gamma^{\prime}$ 代表 $\Gamma ; \mathbf{z}: \sigma$。我们有 $f p i(\Gamma^{\prime})=$ $f p i($ 令 $\Gamma^{\prime}$ 在 $C_{2})=\varnothing$。因此，归纳假设适用于 (2) 并得出令 $\Gamma^{\prime}$ 在 $C_{2}$ 中，$\Gamma^{\prime} \vdash \mathrm{t}_{2}: \mathrm{T}_{2}$ (6)。现在让我们弱化 (5) 和 (6)，使它们成为 HMD-LETGEN 的合适前提。将引理 1.4.2 应用于 (5) 得到 ($\Gamma^{\prime}$ 在 $C_{2}$ 中) $\wedge$ ($\Gamma$ 在 $C_{1}$ 中)，$\Gamma \vdash \mathrm{t}_{1}: \mathrm{T}_{1}$ (7)。将引理 1.4.2 应用于 (6) 得到 ($\Gamma^{\prime}$ 在 $C_{2}$ 中) $\neg \exists \overline{\mathrm{X}}$ ($\Gamma$ 在 $C_{1}$ 中)，$\Gamma^{\prime} \vdash \mathrm{t}_{2}: \mathrm{T}_{2}$ (8)。最后，(3) 意味着 $\overline{\mathrm{X}} \# f t v(\Gamma, \Gamma^{\prime}$ 在 $C_{2}$ 中) (9)。应用 Hmd-LetGen 到 (7)，(9) 和 (8)，我们得到 ($\Gamma^{\prime}$ 在 $C_{2}$ 中) $\wedge \exists \overline{\mathrm{x}}$ ($\Gamma$ 在 $C_{1}$ 中)，$\Gamma \vdash$ 令 $z = \mathrm{t}_{1}$ 在 $\mathrm{t}_{2}: \mathrm{T}_{2}$ 中 (10)。现在，通过 (4)，(3)，以及 C-LetDup，令 $\Gamma^{\prime}$ 在 $C_{2}$ 中等价于令 $\Gamma ; \mathbf{z}: \forall \overline{\mathrm{X}}[C_{1}] . \mathrm{T}_{1}$ 在 $C_{2}$ 中。利用这个事实，以及 (3)，C-InEx 和 C-InAnd，我们发现约束条件 ($\Gamma^{\prime}$ 在 $C_{2}$ 中) $\neg \exists \overline{\mathrm{x}}$ ($\Gamma$ 在 $C_{1}$ 中) 等价于令 $\Gamma$ 在 (令 $\mathrm{z}$: $\forall \overline{\mathrm{X}}[C_{1}] . \mathrm{T}_{1}$ 在 $C_{2} \wedge \exists \overline{\mathrm{x}} . C_{1}$ 中)，根据 let 形式的定义，这本身等价于令 $\Gamma ; z: \forall \overline{\mathrm{X}}[C_{1}] . \mathrm{T}_{1}$ 在 $C_{2}$ 中。最后，根据 $\overline{\mathrm{X

- 案例子。规则的结论是 $C \wedge T \leq T' \vdash t: T'$。它的前提是 $C \vdash t$ : $T$ (1)。将归纳假设应用于(1)得到 let $\Gamma$ in $C, \Gamma \vdash t: T$ (2)。根据引理1.4.2和HMD-Sub，(2)意味着（let $\Gamma$ in $C$）$\wedge T \leq T', \Gamma \vdash t: T'$，通过C-InAnd*可以写成 let $\Gamma$ in $(C \wedge T \leq T'), \Gamma \vdash t: T'$。

$\circ$ 存在案例。规则的结论是 $\exists \overline{\mathrm{x}} . C \vdash \mathrm{t}$ ：T。它的前提是 $C \vdash$ $\mathrm{t}: \mathrm{T}$ （1）和 $\overline{\mathrm{X}} \# \mathrm{ftv}(\mathrm{T})$ （2）。我们还可以进一步要求，不失一般性， $\overline{\mathrm{X}} \# \mathrm{ftv}(\Gamma)$ （3）。将归纳假设应用于（1）得到 let $\Gamma$ in $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$ （4）。将 HmD-Exists 应用于（2），（3）和（4），我们发现 $\exists \overline{\mathrm{X}}$.let $\Gamma$ in $C, \Gamma \vdash \mathrm{t}: \mathrm{T}$，通过（3）和 C-INEx，可以写成 let $\Gamma$ in $\exists \overline{\mathrm{x}} . C, \Gamma \vdash \mathrm{t}: \mathrm{T}$。

作为推论，我们发现对于封闭程序，类型系统$\operatorname{HM}(X)$和$\operatorname{PCB}(X)$是重合的。特别是，一个程序如果在一个系统中是良好类型的，那么它在另一个系统中也是良好类型的。这支持了这样的观点，即$\operatorname{PCB}(X)$是$\operatorname{HM}(X)$的一种替代表述。

1.5.5 定理：假设 $f p i(C)=\varnothing$ 且 $C \not \equiv$ false。那么，在 $\mathrm{HM}(X)$ 中，$C, \varnothing \vdash \mathrm{t}: \mathrm{T}$ 成立当且仅当在 $\operatorname{PCB}(X)$ 中 $C \vdash \mathrm{t}: \mathrm{T}$ 成立。

1.6 约束生成

我们现在解释如何将$\operatorname{PCB}(X)$的类型推断问题简化为约束求解问题。一个类型推断问题由一个表达式组成。

$$
\begin{aligned}
\llbracket \mathrm{x}: \mathrm{T} \rrbracket & =\mathrm{x} \preceq \mathrm{T} \\
\llbracket \lambda \mathrm{z} \cdot \mathrm{t}: \mathrm{T} \rrbracket & =\exists \mathrm{x}_{1} \mathrm{X}_{2} \cdot\left(\text { let } \mathrm{z}: \mathrm{x}_{1} \text { in } \llbracket \mathrm{t}: \mathrm{x}_{2} \rrbracket \wedge \mathrm{X}_{1} \rightarrow \mathrm{x}_{2} \leq \mathrm{T}\right) \\
\llbracket \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T} \rrbracket & =\exists \mathrm{x}_{2} \cdot\left(\llbracket \mathrm{t}_{1}: \mathrm{x}_{2} \rightarrow \mathrm{T} \rrbracket \wedge \llbracket \mathrm{t}_{2}: \mathrm{x}_{2} \rrbracket\right) \\
\llbracket \text { let } \mathrm{z}=\mathrm{t}_{1} \text { in } \mathrm{t}_{2}: \mathrm{T} \rrbracket & =\text { let } \mathrm{z}: \forall \mathrm{x}\left[\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket\right] \cdot \mathrm{X} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket
\end{aligned}
$$

图1-10：约束生成

给定一个项 $t$ 和一个种类为 $\star$ 的类型 $T$。问题是要确定 $t$ 是否与类型 $\mathrm{T}$ 类型兼容，即是否存在一个可满足的约束 $C$ 使得 $C \vdash \mathrm{t}: \mathrm{T}$ 成立。这个问题的表述似乎要求我们事先知道一个合适的类型 $\mathrm{T}$；但实际上并非如此，因为 $\mathrm{T}$ 可以是一个类型变量。约束求解问题由一个约束 $C$ 组成。问题是要确定 $C$ 是否可满足。为了将类型推断问题（$\mathrm{t}, \mathrm{T}$）转化为约束求解问题，我们必须产生一个约束 $C$，它对于 $C \vdash \mathrm{t}: \mathrm{T}$ 成立既是充分的也是必要的。下面，我们解释如何计算这样的约束，我们将其写为 $\llbracket t: T \rrbracket$。我们通过证明 $\llbracket \mathrm{t}: \mathrm{T} \rrbracket \vdash \mathrm{t}: \mathrm{T}$ 来检查它确实是充分的，即，约束 $\llbracket t: T \rrbracket$ 是足够具体的，以确保 $t$ 具有类型 $T$。我们说约束生成是健全的。我们通过证明对于每个约束 $C$，如果 $C \vdash \mathrm{t}: \mathrm{T}$，则 $C \Vdash \llbracket \mathrm{t}: \mathrm{T} \rrbracket$ 来检查它确实是必要的。即，每个保证 $\mathrm{t}$ 有类型 $\mathrm{T}$ 的约束至少与 $\llbracket \mathrm{t}: \mathrm{T} \rrbracket$ 一样具体。我们说约束生成是完整的。这些性质共同意味着 $\llbracket \mathrm{t}: \mathrm{T} \rrbracket$ 是保证 $\mathrm{t}$ 有类型 $\mathrm{T}$ 的最不具体的约束。

我们现在来看看如何将类型推断问题转化为约束求解问题。实际上，如果存在一个可满足的约束C，使得C推导出t属于T成立，那么，根据完整性性质，C证明[t:T]成立，所以[t:T]是可满足的。反之，健全性性质表明[t:T]推导出t属于T成立，因此，如果[t:T]是可满足的，那么存在一个可满足的约束C使得C推导出t属于T成立。换句话说，如果且仅如果[t:T]是可满足的，t才具有类型T。

此类约束的存在类似于ML类型系统（Damas和Milner，1982年）的经典表示中主体类型方案的存在。实际上，主体类型方案在意义上是最不具体的，因为所有有效的类型都是它的替换实例。在这里，约束 $\llbracket t: T \rrbracket$ 在意义上是最不具体的，因为所有有效的约束都蕴含它。早期，我们已经建立了约束蕴含与类型替换细化的联系，特别是在解释有限类型自由代数的等式约束的情况下；参见引理1.3.39。

约束 $\llbracket t: T \rrbracket$ 在图1-10中根据表达式 $t$ 的结构通过归纳定义。我们将这些定义方程称为约束生成规则。这个定义相当简洁。它甚至可能比图1-9中给出的 $\operatorname{PCB}(X)$ 的声明性规范还要简单；然而，我们将在下面证明这两者实际上是等价的。

在解释定义之前，我们提出了与类型变量 $\mathrm{X}_{1}, \mathrm{X}_{2}$ 和 $\mathrm{X}$ 相关的要求，这些类型变量出现在第二、第三和第四个方程式的右侧绑定位置。这些类型变量必须有种类 $\star$。它们必须被选为不同的（即，在第二个方程式中 $\mathrm{X}_{1} \neq \mathrm{X}_{2}$）并且在以下意义上是新鲜的：出现在方程式右侧绑定的类型变量不能在方程式的左侧自由出现。只要遵守这个限制，选择不同的 $\mathrm{X}_{1}, \mathrm{X}_{2}$ 和 $\mathrm{X}$ 会导致 $\alpha$-等价的约束 - 也就是说，相同的约束，因为我们把经过 $\alpha$-转换后相同的对象视为等价 - 这确保了上述方程是有意义的。我们注意到，由于表达式没有自由类型变量，新鲜性的要求可以简化为：出现在方程式右侧绑定的类型变量不能在 T 中自由出现。然而，这种简化由于在表达式中引入类型注释（第102页）而变得无效。请注意，我们能够提出正式的新鲜性要求。这是由于 $\llbracket t: T \rrbracket$ 除了 $\mathrm{T}$ 的类型变量外没有自由类型变量，这又依赖于我们对存在量词的明确使用。

让我们现在回顾一下这四个方程。第一个方程简单地反映了VAR。第二个方程在假设 $z$ 具有类型 $\mathrm{X}_{1}$ 的情况下，要求 $t$ 具有类型 $x_{2}$，并形成箭头类型 $\mathrm{X}_{1} \rightarrow \mathrm{X}_{2}$；这与ABs相对应。在这里，$\mathrm{X}_{1}$ 和 $X_{2}$ 必须是新的类型变量，因为我们通常无法猜测 $z$ 和 $t$ 的预期类型。预期的类型 $\mathrm{T}$ 需要是 $\mathrm{X}_{1} \rightarrow \mathrm{X}_{2}$ 的超类型；这与SUB相对应。我们必须绑定新的类型变量 $\mathrm{X}_{1}$ 和 $\mathrm{X}_{2}$，以确保生成的约束在 $\alpha$-转换下是唯一的。此外，我们必须以存在性方式绑定它们，因为我们希望约束求解器为它们选择一些适当的值。这由Exists证明是合理的。第三个方程使用新的类型变量 $\mathrm{X}_{2}$ 来表示 $t_{2}$ 的未知类型。子表达式 $t_{1}$ 预期具有类型 $\mathrm{X}_{2} \rightarrow \mathrm{T}$。这与APP相对应。第四个方程，对应于LET，是最有趣的。它引入了一个新的类型变量 $\mathrm{X}$ 并产生 $\llbracket t_{1}: x \rrbracket$。这个约束，其唯一的自由类型变量是 $\mathrm{X}$，是必须对 $\mathrm{X}$ 强加的最不具体的约束，以便使它成为 $\mathrm{t}_{1}$ 的有效类型。因此，类型方案 $\forall \mathrm{x}\left[\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket\right] . \mathrm{X}$，以下简称为 $\sigma$，是 $t_{1}$ 的主要类型方案。剩下的是将 $\llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket$ 放在语境 let $\mathrm{z}: \sigma$ in $\square$ 中。实际上，当放在这个语境中时，形式为 $\mathrm{z} \preceq \mathrm{T}^{\prime}$ 的实例化约束获得了含义
$\sigma \preceq \mathrm{T}^{\prime}$，根据 $\sigma$ 的定义和下面提到的引理1.6.4，这等价于 $\llbracket t_{1}: T^{\prime} \rrbracket$。因此，第四个方程产生的约束模拟了let构造的文本展开，即每个出现的 $z$ 都会被替换为 $t_{1}$。由于类型方案引入和实例化约束，这种效果在不复制源代码或约束的情况下实现。换句话说，约束生成具有线性时间和空间复杂性；只有在约束求解过程中可能会发生复制。

1.6.1 练习 $[\star, \nrightarrow]$ ：定义表达式、类型和约束的大小，视为抽象语法树。检查 $\llbracket t: T \rrbracket$ 的大小是否与 $t$ 和 $T$ 大小之和成线性关系。

我们现在建立约束生成的几个性质。我们从完整性开始，其证明是直接的。

1.6.2 定理 [可靠性]：$\mathrm{t}: \mathrm{T} \rrbracket \vdash \mathrm{t}: \mathrm{T}$。

证明：通过对$t$的结构进行归纳。

- 情况 $\mathrm{x}$。目标 $\mathrm{x} \preceq \mathrm{T} \vdash \mathrm{x}: \mathrm{T}$ 来自于 VAR。
- 情况 $\lambda$ z.t. 根据归纳假设，我们有 $\llbracket t: \mathrm{x}_{2} \rrbracket \vdash \mathrm{t}: \mathrm{x}_{2}$。通过 ABs，这意味着 let $\mathrm{z}: \mathrm{x}_{1}$ in $\llbracket \mathrm{t}: \mathrm{x}_{2} \rrbracket \vdash \lambda z$。$\mathrm{t}: \mathrm{x}_{1} \rightarrow \mathrm{X}_{2}$。通过 SuB，这意味着 let $\mathrm{z}: \mathrm{X}_{1}$ in $\llbracket \mathrm{t}: \mathrm{X}_{2} \rrbracket \wedge \mathrm{X}_{1} \rightarrow \mathrm{X}_{2} \leq \mathrm{T} \vdash \lambda \mathrm{z} . \mathrm{t}: \mathrm{T}$。最后，因为 $\mathrm{X}_{1} \mathrm{X}_{2} \# \operatorname{ftv}(\mathrm{T})$ 成立，ExISTS 适用并得到 $\llbracket \lambda z . t: \mathrm{T} \rrbracket \vdash \lambda z . t: \mathrm{T}$。
- 情况 $\mathrm{t}_{1} \mathrm{t}_{2}$。根据归纳假设，我们有 $\llbracket \mathrm{t}_{1}: \mathrm{x}_{2} \rightarrow \mathrm{T} \rrbracket \vdash \mathrm{t}_{1}$ : $\mathrm{x}_{2} \rightarrow \mathrm{T}$ 和 $\llbracket \mathrm{t}_{2}: \mathrm{x}_{2} \rrbracket \vdash \mathrm{t}_{2}: \mathrm{x}_{2}$。通过 APP，这意味着 $\llbracket \mathrm{t}_{1}: \mathrm{x}_{2} \rightarrow \mathrm{T} \rrbracket \wedge$ $\llbracket \mathrm{t}_{2}: \mathrm{X}_{2} \rrbracket \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}$。因为 $\mathrm{X}_{2} \notin f t v(\mathrm{~T})$ 成立，ExISTs 适用并得到 $\llbracket \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T} \rrbracket \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}$。
- 情况 let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}$。根据归纳假设，我们有 $\llbracket \mathrm{t}_{1}$ : $\mathrm{x} \rrbracket \vdash \mathrm{t}_{1}: \mathrm{x}$ 和 $\llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket \vdash \mathrm{t}_{2}:$ T。通过 LET，这些意味着 let $\mathrm{z}: \forall \mathcal{V}\left[\llbracket \mathrm{t}_{1}:\right.$ $\mathrm{x} \rrbracket] . \mathrm{X}$ in $\llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket \vdash$ let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}$。因为 $\mathrm{ftv}\left(\llbracket \mathrm{t}_{1}: \mathrm{X} \rrbracket\right)$ 是 $\mathrm{X}$，对 $\mathcal{V}$ 的全称量化实际上只针对 $X$。我们已经证明了 $\llbracket l$ et $z=t_{1}$ in $t_{2}$ : $\mathrm{T} \rrbracket \vdash$ let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}$。

以下引理在证明完备性属性以及在许多其他场合被使用。前两个陈述了 $\llbracket t: T \rrbracket$ 关于 $\mathrm{T}$ 是协变的。粗略地说，这意味着生成了足够的子类型约束以达到关于SUB的完备性。

1.6.3 引理：$\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{T}^{\prime}$ 推出 $\llbracket \mathrm{t}: \mathrm{T}^{\prime} \rrbracket$.

1.6.4 引理：$\mathrm{X} \notin ftv(\mathrm{~T})$ 意味着 $\exists \mathrm{X} .(\llbracket \mathrm{t}: \mathrm{X} \rrbracket \wedge \mathrm{X} \leq \mathrm{T})$ 等价于 $\llbracket \mathrm{t}: \mathrm{T} \rrbracket$.

下一个引理给出了在期望类型为箭头类型的特定情况下第二个约束生成规则的简化版本。在这种情况下，不需要生成新的类型变量；可以直接使用箭头的域和余域。

引理：$\llbracket \lambda$ z.t : $\mathrm{T}_{1} \rightarrow \mathrm{T}_{2} \rrbracket$ 等价于让 $\mathrm{z}: \mathrm{T}_{1}$ 在 $\llbracket \mathrm{t}: \mathrm{T}_{2} \rrbracket$ 中。

我们以完备性属性作结。

1.6.6 定理 [完整性]：如果 $C \vdash \mathrm{t}: \mathrm{T}$，那么 $C \Vdash \llbracket \mathrm{t}: \mathrm{T} \rrbracket$.

证明：通过对$C \vdash \mathrm{t}: \mathrm{T}$的推导进行归纳。

案例 VAR。规则的结论是 $C \vdash \mathrm{x}$ : T。其前提是 $C \Vdash \mathrm{x} \preceq \mathrm{T}$，这也是目标。

- AB案例。规则的结论是令 $z : \mathrm{T}$ 在 $C \vdash \lambda z . t: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$。其前提是 $C \vdash \mathrm{t}: \mathrm{T}^{\prime}$。根据归纳假设，我们有 $C \Vdash \llbracket \mathrm{t}: \mathrm{T}^{\prime} \rrbracket$。根据蕴含的等价性，这意味着令 $z : \mathrm{T}$ 在 $C \Vdash$ 令 $z : \mathrm{T}$ 在 $\llbracket \mathrm{t}: \mathrm{T}^{\prime} \rrbracket$，根据引理1.6.5，可以写成令 $z : \mathrm{T}$ 在 $C \Vdash \llbracket \lambda z . \mathrm{t}: \mathrm{T} \rightarrow \mathrm{T}^{\prime} \rrbracket$。
- App案例。规则的结论是 $C_{1} \wedge C_{2} \vdash \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime}$。其前提是 $C_{1} \vdash \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$ 和 $C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}$。根据归纳假设，我们有 $C_{1} \Vdash \llbracket \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime} \rrbracket$ 和 $C_{2} \Vdash \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket$。因此，$C_{1} \wedge C_{2}$ 蕴含 $\llbracket \mathrm{t}_{1}: \mathrm{T} \rightarrow \mathrm{T}^{\prime} \rrbracket \wedge \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket$，根据C-NAMEEQ，可以写成 $\exists \mathrm{X}_{2} \cdot\left(\mathrm{X}_{2}=\mathrm{T} \wedge \llbracket \mathrm{t}_{1}: \mathrm{X}_{2} \rightarrow \mathrm{T}^{\prime} \rrbracket \wedge \llbracket \mathrm{t}_{2}: \mathrm{X}_{2} \rrbracket\right)$，其中 $\mathrm{X}_{2} \notin f t v\left(\mathrm{~T}, \mathrm{~T}^{\prime}\right)$。忽略方程 $\mathrm{X}_{2}=\mathrm{T}$，我们发现 $C_{1} \wedge C_{2}$ 蕴含 $\exists \mathrm{X}_{2} \cdot\left(\llbracket \mathrm{t}_{1}: \mathrm{X}_{2} \rightarrow \mathrm{T}^{\prime} \rrbracket \wedge \llbracket \mathrm{t}_{2}: \mathrm{X}_{2} \rrbracket\right)$，这正是 $\llbracket \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime} \rrbracket$。
- Let案例。规则的结论是令 $\mathrm{z}: \forall \mathcal{V}\left[C_{1}\right] . \mathrm{T}_{1}$ 在 $C_{2} \vdash$ 令 $\mathrm{z}=$ $\mathrm{t}_{1}$ 在 $\mathrm{t}_{2}: \mathrm{T}_{2}$。其前提是 $C_{1} \vdash \mathrm{t}_{1}: \mathrm{T}_{1}$ 和 $C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}_{2}$。根据归纳假设，我们有 $C_{1} \Vdash \llbracket \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket$ 和 $C_{2} \Vdash \llbracket \mathrm{t}_{2}: \mathrm{T}_{2} \rrbracket$，这意味着令 $\mathrm{z}: \forall \mathcal{V}\left[C_{1}\right] . \mathrm{T}_{1}$ 在 $C_{2} \Vdash$ 令 $\mathrm{z}: \forall \mathcal{V}\left[\llbracket \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket\right] . \mathrm{T}_{1}$ 在 $\llbracket \mathrm{t}_{2}: \mathrm{T}_{2} \rrbracket$ (1)。

现在，让我们证明真正的 $\Vdash \forall \mathrm{x}\left[\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket\right] . \mathrm{x} \preceq \forall \mathcal{V}\left[\llbracket \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket\right] . \mathrm{T}_{1}$ (2)。根据定义，这需要证明 $\exists \overline{\mathrm{X}}_{1} \cdot\left(\llbracket \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket \wedge \mathrm{T}_{1} \leq \mathrm{Z}\right) \Vdash \exists \mathrm{X} .\left(\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket \wedge \mathrm{X} \leq\right.$ Z) (3)，其中 $\overline{\mathrm{X}}_{1}=f t v\left(\mathrm{~T}_{1}\right)$ 且 $\mathrm{Z} \notin \mathrm{X} \overline{\mathrm{X}}_{1}$ (4)。根据引理1.6.3、(4)和CEx*，(3)式的左边蕴含 $\llbracket t_{1}: \mathrm{z} \rrbracket$。由(4)和引理1.6.4，(3)式的右边是 $\llbracket t_{1}: z \rrbracket$。因此，(3)成立，(2)也成立。

由 $(2)$ 和引理1.3.22，我们得到 $\mathrm{z}: \forall \mathcal{V}\left[\llbracket \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket\right] . \mathrm{T}_{1}$ 在 $\llbracket \mathrm{t}_{2}: \mathrm{T}_{2} \rrbracket$ 中成立，即 let $\mathrm{z}: \forall \mathrm{X}\left[\llbracket \mathrm{t}_{1}: \mathrm{X} \rrbracket\right] \cdot \mathrm{X}$ 在 $\llbracket \mathrm{t}_{2}: \mathrm{T}_{2} \rrbracket$ 中（5）。由于蕴含的传递性，（1）和（5）得出 let $\mathrm{z}: \forall \mathcal{V}\left[C_{1}\right] . \mathrm{T}_{1}$ 在 $C_{2}$ 中成立，即 $\Vdash \llbracket$ let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}: \mathrm{T}_{2} \rrbracket$。

- 案例子。规则的结论是 $C \wedge T \leq T' \vdash t: T'$。它的前提是 $C \vdash t: T$。根据归纳假设，我们得到 $C \Vdash \llbracket t: T \rrbracket$，这意味着 $C \wedge T \leq T' \Vdash \llbracket t: T \rrbracket \wedge T \leq T'$。根据引理1.6.3和蕴含的传递性，我们得到 $C \wedge T \leq T' \Vdash \llbracket t: T' \rrbracket$。

存在案例。规则的结论是 $\exists \overline{\mathrm{x}} . C \vdash \mathrm{t}$ ： $\mathrm{T}$。它的前提是 $C \vdash \mathrm{t}: \mathrm{T}$ 和 $\overline{\mathrm{x}} \# f t v(\mathrm{~T})$ (1)。根据归纳假设，我们有 $C \Vdash \llbracket \mathrm{t}: \mathrm{T} \rrbracket$。

通过蕴含的同一性，这暗示存在 $\exists \overline{\mathrm{X}} . C \Vdash \exists \overline{\mathrm{X}}$. $\mathrm{t}: \mathrm{T} \rrbracket$ (2)。此外，（1）意味着 $\overline{\mathrm{X}}$ \# ftv( $\llbracket \mathrm{t}: \mathrm{T} \rrbracket)$ (3)。由（3）和C-Ex*，（2）可以写作 $\exists \overline{\mathrm{x}} . C \Vdash \llbracket \mathrm{t}: \mathrm{T} \rrbracket$。

### 1.7 类型安全性能

我们现在准备为我们的类型系统建立类型健全性。我们希望证明的陈述有时被称为Milner的口号：良好类型化的程序不会出错（Milner，1978年）。下面，我们为了方便起见，根据我们的约束生成规则来定义良好类型性，并基于那个特定的定义建立类型健全性。定理1.4.7、1.5.4和1.6.6表明，当良好类型性是相对于$\mathrm{DM}$、$\operatorname{HM}(X)$或$\mathrm{PCB}(X)$的类型判断定义时，类型健全性同样成立。我们通过遵循Wright和Felleisen所谓的句法方法（1994b）来建立类型健全性。这种方法包括隔离两个独立属性。主题还原，其确切陈述将在下面给出，意味着良好类型性通过还原得到保持。进展性陈述没有陷入困境的配置是良好类型化的。立即可以验证，如果这两个属性都成立，那么没有良好类型化的程序可以还原到陷入困境的配置。主题还原本身依赖于一个关键引理，通常称为（项）替换引理。我们立即给出这个引理的两个版本：前者是用$\operatorname{PCB}(X)$判断来陈述的，而后者是用约束生成规则来陈述的。

1.7.1 引理 [替换]：若 $C \vdash \mathrm{t}: \mathrm{T}$ 和 $C_{0} \vdash \mathrm{t}_{0}: \mathrm{T}_{0}$，则令 $\mathrm{z}_{0}$ : $\forall \overline{\mathrm{x}}_{0}\left[C_{0}\right] . \mathrm{T}_{0}$ 在 $C \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}: \mathrm{T}$.

证明：证明是对 $C \vdash \mathrm{t}: \mathrm{T}$ 的推导结构归纳。在每个证明情形中，我们采用图1-9的记号。我们用 $\sigma_{0}$ 表示 $\forall \overline{\mathrm{x}}_{0}\left[C_{0}\right] . \mathrm{T}_{0}$。我们将假设 $C_{0} \vdash \mathrm{t}_{0}: \mathrm{T}_{0}$ 称为（1）。我们假设，不失一般性，$\overline{\mathrm{X}}_{0} \# \operatorname{ftv}(C, \mathrm{~T})$（2）以及 $\mathrm{z}_{0} \notin f p i\left(\sigma_{0}\right)$ （3）。

案件VAR。规则的结论是 $C \vdash \mathrm{x}: \mathrm{T}$ (4)。其前提是 $C \Vdash \mathrm{x} \preceq$ $\mathrm{T}$ (5)。分为两种子情况。

子案例 $\mathrm{x}$ 是 $\mathrm{z}_{0}$。将Sub应用于(1)得到 $C_{0} \wedge \mathrm{T}_{0} \leq \mathrm{T} \vdash \mathrm{t}_{0}$ : T。根据(2)和存在量词，这意味着 $\exists \overline{\mathrm{X}}_{0} \cdot\left(C_{0} \wedge \mathrm{T}_{0} \leq \mathrm{T}\right) \vdash \mathrm{t}_{0}: \mathrm{T}$ (6)。再者，根据(2)的再次应用，约束 $\exists \overline{\mathrm{X}}_{0} \cdot\left(C_{0} \wedge \mathrm{T}_{0} \leq \mathrm{T}\right)$ 是 $\sigma_{0} \preceq \mathrm{T}$，这等同于让 $\mathrm{z}_{0}: \sigma_{0}$ 使得 $\mathrm{z}_{0} \preceq \mathrm{T}$。因此，(6)可以写成让 $\mathrm{z}_{0}: \sigma_{0}$ 使得 $\mathrm{x} \preceq \mathrm{T} \vdash$ $\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{x}: \mathrm{T}(\mathbf{7})$。

子情况 $\mathrm{x}$ 不是 $\mathrm{z}_{0}$。那么，$\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{x}$ 就是 $\mathrm{x}$。因此，VAR引出 $\exists \sigma_{0} \wedge \mathrm{x} \preceq \mathrm{T} \vdash$ $\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{x}: \mathrm{T}$。根据C-IN*，这可以读作让 $\mathrm{z}_{0}: \sigma_{0}$ 在 $\mathrm{x} \preceq \mathrm{T} \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{x}$ ：$\mathrm{T}$，即，再次（7）。

在任一子情况中，根据（5），根据蕴含的相等性，以及根据引理1.5.2，（7）意味着令 $\mathrm{z}_{0}: \sigma_{0}$ 在 $C \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}: \mathrm{T}$。

- ABs案例。规则的结论是让 $\mathrm{z}: \mathrm{T}$ 在 $C \vdash \lambda$ z.t : $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$。其前提是 $C \vdash \mathrm{t}: \mathrm{T}^{\prime}(\mathbf{8})$。我们可以假设，不失一般性，$\mathrm{z}$ 与 $\mathrm{z}_{0}$ 不同，并且不自由出现在 $t_{0}$ 或 $\sigma_{0}(9)$ 中。将归纳假设应用于（8）得到让 $\mathrm{z}_{0}: \sigma_{0}$ 在 $C \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}: \mathrm{T}^{\prime}$，通过 ABs，这意味着让 $\mathrm{z}: \mathrm{T}$ 在（让 $\mathrm{z}_{0}: \sigma_{0}$ 在 $\left.C\right)$ 中 $\vdash \lambda \mathrm{z}$. $\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}: \mathrm{T} \rightarrow \mathrm{T}^{\prime}$。通过（9）和 C-LETLet，这可以写成让 $\mathrm{z}_{0}: \sigma_{0}$ 在（让 $\mathrm{z}: \mathrm{T}$ 在 $\left.C\right)$ 中 $\vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right](\lambda \mathrm{z} . \mathrm{t}): \mathrm{T} \rightarrow \mathrm{T}^{\prime}$。
- APP案例。根据归纳假设、APP 规则和 C-InAnd。
- LET案例。规则的结论是让 $\mathrm{z}: \forall \overline{\mathrm{x}}_{1}\left[C_{1}\right] . \mathrm{T}_{1}$ 在 $C_{2} \vdash$ 让 $\mathrm{z}=$ $\mathrm{t}_{1}$ 在 $\mathrm{t}_{2}: \mathrm{T}_{2}$，其中 $\overline{\mathrm{x}}_{1}=\operatorname{ftv}\left(C_{1}, \mathrm{~T}_{1}\right)$。其前提是 $C_{1} \vdash \mathrm{t}_{1}: \mathrm{T}_{1}(\mathbf{1 0})$ 和 $C_{2} \vdash \mathrm{t}_{2}: \mathrm{T}_{2}$ (11)。我们可以假设，不失一般性，$\mathrm{z}$ 与 $\mathrm{z}_{0}$ 不同，并且不自由出现在 $\mathrm{t}_{0}$ 或 $\sigma_{0}$ (12) 中。我们还可以假设，不失一般性，$\overline{\mathrm{x}}_{1} \#$ $f t v\left(\sigma_{0}\right)$ (13)。将归纳假设分别应用于（10）和（11）得到让 $\mathrm{z}_{0}: \sigma_{0}$ 在 $C_{1} \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}_{1}: \mathrm{T}_{1}(\mathbf{1 4})$ 和让 $\mathrm{z}_{0}: \sigma_{0}$ 在 $C_{2} \vdash\left[\mathrm{z}_{0} \mapsto\right.$ $\left.\mathrm{t}_{0}\right] \mathrm{t}_{2}: \mathrm{T}_{2}$ (15)。将 LET 规则应用于（14）和（15）产生让 $\mathrm{z}: \forall \mathcal{V}\left[\right.$ 让 $\mathrm{z}_{0}:$ $\sigma_{0}$ 在 $\left.C_{1}\right] . \mathrm{T}_{1}$ 在让 $\mathrm{z}_{0}: \sigma_{0}$ 在 $C_{2} \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right]$ (让 $\mathrm{z}=\mathrm{t}_{1}$ 在 $\left.\mathrm{t}_{2}\right): \mathrm{T}_{2}$ (16)。现在，我们有

$$
\begin{array}{ll} 
& \text { let } \mathrm{z}_{0}: \sigma_{0} ; \mathrm{z}: \forall \overline{\mathrm{X}}_{1}\left[C_{1}\right] \cdot \mathrm{T}_{1} \text { in } C_{2} \\
\equiv & \text { let } \mathrm{z}_{0}: \sigma_{0} ; \mathrm{z}: \forall \overline{\mathrm{X}}_{1}\left[\text { let } \mathrm{z}_{0}: \sigma_{0} \text { in } C_{1}\right] \cdot \mathrm{T}_{1} \text { in } C_{2} \\
\equiv & \text { let } \mathrm{z}: \forall \overline{\mathrm{X}}_{1}\left[\text { let } \mathrm{z}_{0}: \sigma_{0} \text { in } C_{1}\right] \cdot \mathrm{T}_{1} ; \mathrm{z}_{0}: \sigma_{0} \text { in } C_{2} \\
\Vdash & \text { let } \mathrm{z}: \forall \mathcal{V}\left[\text { let } \mathrm{z}_{0}: \sigma_{0} \text { in } C_{1}\right] \cdot \mathrm{T}_{1} ; \mathrm{z}_{0}: \sigma_{0} \text { in } C_{2} \tag{19}
\end{array}
$$

其中（17）由（13）、（3）和C-LETDup得出；（18）由（12）和C-LetLet得出；而（19）根据引理1.3.25。因此，将引理1.5.2应用于（16）得到 let $\mathrm{z}_{0}: \sigma_{0} ; \mathrm{z}: \forall \overline{\mathrm{x}}_{1}\left[C_{1}\right] . \mathrm{T}_{1}$ 在 $C_{2} \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right]$ （在 $\left.\mathrm{t}_{2}\right)$ 中 let $\mathrm{z}=\mathrm{t}_{1}$ ): $\mathrm{T}_{2}$。

- 子情况。根据归纳假设，根据子情况，以及根据C-InAnd*。
- 存在情况。规则的结论是 $\exists \overline{\mathrm{x}} . C \vdash \mathrm{t}$ : T。它的前提是 $C \vdash$ $\mathrm{t}: \mathrm{T}$ (20) 和 $\overline{\mathrm{X}} \# \mathrm{ftv}(\mathrm{T})$ (21)。我们可以假设，不失一般性，$\overline{\mathrm{X}} \# \mathrm{ftv}\left(\sigma_{0}\right)$ (22)。将归纳假设应用于(20)得到 let $\mathrm{z}_{0}: \sigma_{0}$ in $C \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}$ : $\mathrm{T}$，这由(21)和ExisTs，意味着 $\exists \overline{\mathrm{x}}$。let $\mathrm{z}_{0}: \sigma_{0}$ in $C \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}: \mathrm{T}$ (23)。由(22)和C-InEx，(23)是 let $\mathrm{z}_{0}: \sigma_{0}$ in $\exists \overline{\mathrm{x}} . C \vdash\left[\mathrm{z}_{0} \mapsto \mathrm{t}_{0}\right] \mathrm{t}: \mathrm{T}$。

1.7.2 引理：令 $\mathrm{z}: \forall \overline{\mathrm{X}}\left[\llbracket \mathrm{t}_{2}: \mathrm{T}_{2} \rrbracket\right] \cdot \mathrm{T}_{2}$ 在 $\llbracket \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket$ 中蕴含 $\llbracket\left[\mathrm{z} \mapsto \mathrm{t}_{2}\right] \mathrm{t}_{1}: \mathrm{T}_{1} \rrbracket$。

在继续之前，让我们给出几个定义并制定几项要求。首先，我们必须定义一个初始环境 $\Gamma_{0}$，它为每个常数分配一个类型方案。必须提出一些要求以确保 $\Gamma_{0}$ 与常数的语义一致，如 $\xrightarrow{\delta}$ 所指定。其次，我们必须将约束生成和类型健全性扩展到配置，而不是程序，因为简化操作是在配置上进行的。

最后，我们必须制定一个限制来控制副作用之间的交互以及let多态性，如果不受限制，这是不健全的。

1.7.3 定义：设 $\Gamma_{0}$ 是一个环境，其域是常数集合 $\mathcal{Q}$。我们需要 $f t v\left(\Gamma_{0}\right)=\varnothing$，fpi $\left(\Gamma_{0}\right)=\varnothing$，以及 $\exists \Gamma_{0} \equiv$ true。我们将 $\Gamma_{0}$ 称为初始类型环境。

1.7.4 定义：设ref是一个孤立的、不变的类型构造器，其签名是 $\star \Rightarrow \star$。存储类型$M$是从内存位置到类型的有限映射。当$m$在$M$的定义域内时，我们用ref $M$表示将$m$映射到$\operatorname{ref} M(m)$的环境。假设$\operatorname{dom}(\mu)$和$\operatorname{dom}(M)$相同，约束$\llbracket \mu: M \rrbracket$被定义为约束$\llbracket \mu(m): M(m) \rrbracket$的连结，其中$m$遍历$\operatorname{dom}(\mu)$。在相同假设下，约束$\llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket$被定义为$\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \llbracket \mu: M \rrbracket$。配置$\mathrm{t} / \mu$是类型正确的当且仅当存在一个类型$\mathrm{T}$和一个存储类型$M$使得$\operatorname{dom}(\mu)=\operatorname{dom}(M)$并且约束let $\Gamma_{0} ;$ ref $M$ in $\llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket$是可满足的。

类型引用 $\mathrm{T}$ 是存储类型 T 数据的引用（即内存位置）的类型。它在参数上必须是不变的，反映了引用可能被读取和写入的事实。

一个存储是一个复杂的对象：它可能包含通过内存位置间接引用彼此的值。实际上，它是内存中对象和指针形成的图的表示，可能包含循环。我们依赖存储类型来处理这样的循环。在良好类型定义中，存储类型$M$对存储内容施加了一个约束——值$\mu(m)$必须有类型$M(m)$——但也扮演着假设的角色：通过在上下文let ref $M$ in []中放置约束$\llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket$，我们给出了内存位置在$\llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket$中自由出现的含义，并规定假设$m$有类型$M(m)$是有效的。换句话说，我们基本上将存储看作是位置到值的大的相互递归绑定。由于没有可满足的约束可能包含自由程序标识符（引理1.3.31），每个良好类型的配置必须是封闭的。上下文let $\Gamma_{0}$ in []给出了常量在$\llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket$中出现含义。

我们现在定义了一个配置之间的关系，这在主题约简属性的陈述中扮演了关键角色。主题约简的要点是保证类型正确性通过约简得到保持。然而，这样一个简单的陈述对于归纳证明来说过于薄弱。因此，为了证明的目的，我们必须更加具体。首先，让我们考虑一个更简单的情况，即纯语义，也就是没有存储的语义。然后，我们必须陈述，如果在一定的约束下表达式$t$具有类型$T$，那么它的约简形式$t^{\prime}$在相同的约束下也具有类型$T$。在生成约束的表述中，这个陈述变成了：令$\Gamma_{0}$在$\llbracket t: T \rrbracket$中蕴含着令$\Gamma_{0}$在$\llbracket t^{\prime}: T \rrbracket$中。

让我们现在回到一般情况，其中存在一个商店。那么，配置 $t / \mu$ 的良好类型声明涉及一个存储类型 $M$，其域是 $\mu$ 的域。因此，其简化 $\mathrm{t}^{\prime} / \mu^{\prime}$ 的良好类型声明必须涉及一个存储类型 $M^{\prime}$，其域是 $\mu^{\prime}$ 的域——如果发生了分配，这个域会更大。现有内存位置的类型不得更改：我们必须要求 $M$ 和 $M^{\prime}$ 在 $\operatorname{dom}(M)$ 上达成一致，即 $M^{\prime}$ 必须扩展 $M$。此外，分配给 $\operatorname{dom}\left(M^{\prime}\right) \backslash \operatorname{dom}(M)$ 中新内存位置的类型可能涉及新的类型变量，即那些在 $M$ 或 $T$ 中没有自由出现的变量。我们必须允许这些变量被隐藏——即存在性地量化——否则蕴含断言无法成立。这些考虑引导我们得到以下定义：

1.7.5 定义：$\mathrm{t} / \mu \sqsubseteq \mathrm{t}^{\prime} / \mu^{\prime}$ 成立当且仅当，对于任意类型 $\mathrm{T}$ 和任意存储类型 $M$ 使得 $\operatorname{dom}(\mu)=\operatorname{dom}(M)$，存在一组类型变量 $\overline{\mathrm{Y}}$ 和一个存储类型 $M^{\prime}$ 使得 $\overline{\mathrm{Y}} \# f t v(\mathrm{~T}, M)$ 和 $f t v\left(M^{\prime}\right) \subseteq \overline{\mathrm{Y}} \cup f t v(M)$ 并且 $\operatorname{dom}\left(M^{\prime}\right)=\operatorname{dom}\left(\mu^{\prime}\right)$ 且 $M^{\prime}$ 扩展自 $M$ 以及

$$
\begin{gathered}
\text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket \\
\Vdash \exists \overline{\mathrm{Y}} \text {.let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket \mathrm{t}^{\prime} / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket
\end{gathered}
$$

关系 $\sqsubseteq$ 旨在表达配置与其约简之间的联系。因此，主题约简可以表述为：$(\longrightarrow) \subseteq(\sqsubseteq)$，即 $\sqsubseteq$ 实际上是对约简的保守描述。

我们已经引入了一个初始环境 $\Gamma_{0}$，并在类型良构性的定义中使用了它，但我们还没有确保分配给常量的类型方案能够充分描述它们的语义。现在我们制定了两个要求，将 $\Gamma_{0}$ 与 $\xrightarrow{\delta}$ 相关联。它们是主题还原和进步性质针对涉及常量应用配置的特殊化。它们表示在给出 $\mathcal{Q}, \xrightarrow{\delta}$ 和 $\Gamma_{0}$ 的具体定义时必须履行证明义务。

1.7.6 定义：我们需要（i）$(\xrightarrow{\delta}) \subseteq(\sqsubseteq)$；以及（ii）如果配置 $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$（其中 $k \geq 0$）是良类型的，那么它要么是可约的，要么 c $\mathrm{v}_{1} \ldots \mathrm{v}_{k}$ 是一个值。

在证明类型安全之前，最后一个需要解决的问题是副作用与let多态性之间的交互。以下示例说明了这个问题：

$$
\text { let } r=\text { ref } \lambda z . z \text { in let }{ }_{-}=(r:=\lambda z \cdot(z \hat{+} \hat{1})) \text { in } ! \text { true }
$$

这个表达式简化为真的 $\hat{+} \hat{1}$，所以它必须是类型良好的。然而，如果将自然的类型方案分配给ref、! 和 $:=$（参见示例1.9.5），那么根据到目前为止给出的规则，它是类型良好的，因为 $\mathrm{r}$ 接收到了多态类型方案 $\forall \mathrm{X}$. $\operatorname{ref}(\mathrm{X} \rightarrow \mathrm{X})$，这允许将类型为int $\rightarrow$ int的函数写入 $\mathrm{r}$ 并以类型bool $\rightarrow$ bool读取它。问题是，let多态模拟了letbound表达式ref $\lambda z . z$的文本复制，而语义首先将其简化为值$m$，导致在存储中出现了新的绑定 $m \mapsto \lambda z . z$，然后复制了地址$m$。新的存储绑定没有复制：$m$的两个副本都指向同一个内存单元。因此，在这种情况下，泛化是不健全的，必须受到限制。许多作者试图提出一个健全的类型系统，接受所有纯程序，并在副作用存在时保持足够的灵活性（Tofte，1988；Leroy，1992）。这些提议通常很复杂，这就是为什么它们被放弃，转而支持一种极为简单的语法限制，称为值限制（Wright，1995）。

1.7.7 定义：一个程序满足值限制，当且仅当所有形如 let $z=t_{1}$ in $t_{2}$ 的子表达式实际上都是形如 let $z=v_{1}$ in $t_{2}$ 的形式。在以下内容中，我们假设所有常量都具有纯语义，或者所有程序都满足值限制。

换种说法，值限制规定只能将值泛化。这完全消除了问题，因为复制值不会影响程序的语义。请注意，任何不满足值限制的程序都可以转换为满足值限制且具有相同语义的程序：只需将 $t_{2}$ 中的 let $z=t_{1}$ 改为 $\left(\lambda z . t_{2}\right) t_{1}$，其中 $t_{1}$ 不是值。当然，这种转换可能导致程序变成类型不正确。换句话说，值限制导致一些完全安全的程序被拒绝。特别是，如上所述，它阻止了形如 $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k}$ 的应用的一般化，其中 $\mathrm{c}$ 是 arity $k$ 的析构函数。这是过度的，因为许多析构函数具有纯语义；只有少数，如 ref，分配新的可变存储。此外，我们使用纯析构函数来编码许多语言特性（第1.9节）。幸运的是，放宽限制以允许不仅泛化值，还允许泛化不能分配新的可变存储（即扩展存储域）的非扩展表达式是很容易的。这一术语由Tofte（1988）提出。非扩展表达式可能包括形如 $\mathrm{c} \mathrm{t}_{1} \ldots \mathrm{t}_{k}$ 的应用，其中 $\mathrm{c}$ 是 arity $k$ 的纯析构函数，而 $t_{1}, \ldots, t_{k}$ 是非扩展的。经验表明，这种稍微放宽的限制在实践中是可以接受的。还有一些对值限制的其他改进；例如，参见练习（Garrigue，2002）。值限制的另一个常见限制是构造函数，即只构建值的函数，这些函数被视为普通函数而不是构造函数，它们的应用也不被认为是值。例如，在表达式 let $f=c v$ in let $z=f$ w in $t$ 中，其中 $\mathrm{c}$ 是 arity 2 的构造函数，绑定到 $f$ 的部分应用 $\mathrm{c} v$ 是一个构造函数（arity 1），但 $f \mathrm{w}$ 被视为常规应用，不能被泛化。技术上，(严格)值限制的效果可以通过以下结果来总结。

1.7.8 引理：在值限制下，产生式 $\mathcal{E}::=$ let $\mathrm{z}=\mathcal{E}$ in $\mathrm{t}$ 可以从评估上下文语法（图1-1）中省略，而不会改变操作语义。

我们已经完成了定义和要求的讨论。现在我们来到了类型健全性证明的核心部分。

1.7.9 定理 [主题简化]：$(\longrightarrow) \subseteq(\sqsubseteq)$。

证明：因为 $\longrightarrow$ 和 $\longrightarrow$ 是满足图1-2规则的最小关系，因此只需证明 $\sqsubseteq$ 也满足这些规则。我们注意到，如果对于每种类型 $\mathrm{T}$ ， $\llbracket \mathrm{t}: \mathrm{T} \rrbracket \Vdash \llbracket \mathrm{t}^{\prime}: \mathrm{T} \rrbracket$ 成立，那么 $\mathrm{t} / \mu \sqsubseteq \mathrm{t}^{\prime} / \mu$ 也成立。（取 $\overline{\mathrm{Y}}=\varnothing$ 和 $M^{\prime}=M$ ，并利用蕴含是一种同余关系的事实来检查定义1.7.5的条件是否满足。）我们在下面的情况 R-BETA 和 R-LET 中利用这个事实。

- R-贝塔案例。我们有了

$$
\begin{align*}
& \llbracket(\lambda z . t) \mathrm{v}: \mathrm{T} \rrbracket \\
\equiv & \exists \mathrm{x} .(\llbracket \lambda \mathrm{z} . \mathrm{t}: \mathrm{X} \rightarrow \mathrm{T} \rrbracket \wedge \llbracket \mathrm{v}: \mathrm{x} \rrbracket)  \tag{1}\\
\equiv & \exists \mathrm{x} .(\text { let } \mathrm{z}: \mathrm{X} \text { in } \llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \llbracket \mathrm{v}: \mathrm{x} \rrbracket)  \tag{2}\\
\equiv & \exists \mathrm{x} . \text { let } \mathrm{z}: \forall \varnothing[\llbracket \mathrm{v}: \mathrm{x} \rrbracket] . \mathrm{X} \text { in } \llbracket \mathrm{t}: \mathrm{T} \rrbracket  \tag{3}\\
\Vdash & \llbracket[\mathrm{z} \mapsto \mathrm{v}] \mathrm{t}: \mathrm{T} \rrbracket \tag{4}
\end{align*}
$$

其中（1）是根据约束生成的定义；（2）是根据引理1.6.5；（3）是根据C-LetAnd；（4）是根据引理1.7.2和C-Ex*。

- R-LET案例。我们有

$$
\begin{align*}
& \llbracket \text { let } \mathrm{z}=\mathrm{v} \text { in } \mathrm{t}: \mathrm{T} \rrbracket \\
= & \text { let } \mathrm{z}: \forall \mathrm{x}[\llbracket \mathrm{v}: \mathrm{x} \rrbracket] \cdot \mathrm{X} \text { in } \llbracket \mathrm{t}: \mathrm{T} \rrbracket  \tag{1}\\
\mathbb{} & \llbracket[\mathrm{z} \mapsto \mathrm{v}] \mathrm{t}: \mathrm{T} \rrbracket \tag{2}
\end{align*}
$$

其中（1）是根据约束生成的定义，（2）是根据引理1.7.2。

- R-Delta案例。这个案例正好符合定义1.7.6中的要求(i)。
- R-Extend案例。我们的假设是 $\mathrm{t} / \mu \sqsubseteq \mathrm{t}^{\prime} / \mu^{\prime}(\mathbf{1})$ 和 $\operatorname{dom}\left(\mu^{\prime \prime}\right) \#$ $\operatorname{dom}\left(\mu^{\prime}\right)$ (2) 以及 range( $\left.\mu^{\prime \prime}\right) \# \operatorname{dom}\left(\mu^{\prime} \backslash \mu\right)$ (3)。因为 $\operatorname{dom}(\mu)$ 必须是 $\operatorname{dom}\left(\mu^{\prime}\right)$ 的子集，所以它也与 $\operatorname{dom}\left(\mu^{\prime \prime}\right)$ 不相交。我们的目标是 $\mathrm{t} / \mu \mu^{\prime \prime} \sqsubseteq$ $\mathrm{t}^{\prime} / \mu^{\prime} \mu^{\prime \prime}(4)$。因此，让我们引入一个类型 $\mathrm{T}$ 和一个域为 $\operatorname{dom}\left(\mu \mu^{\prime \prime}\right)$ 的存储类型，或者（等价地）两个存储类型 $M$ 和 $M^{\prime \prime}$，它们的域分别是 $\operatorname{dom}(\mu)$ 和 $\operatorname{dom}\left(\mu^{\prime \prime}\right)$。根据(1)，存在类型变量 $\overline{\mathrm{Y}}$ 和一个存储类型 $M^{\prime}$ 使得 $\overline{\mathrm{Y}} \# f t v(\mathrm{~T}, M)$ (5) 和 $f t v\left(M^{\prime}\right) \subseteq \overline{\mathrm{Y}} \cup f t v(M)$ 以及 $\operatorname{dom}\left(M^{\prime}\right)=\operatorname{dom}\left(\mu^{\prime}\right)$ 和 $M^{\prime}$ 扩展 $M$ (6) 并设 $\Gamma_{0}$; ref $M$ 在 $\llbracket \mathrm{t} / \mu$ : $\mathrm{T} / M \rrbracket \Vdash \exists \overline{\mathrm{Y}}$。设 $\Gamma_{0}$; ref $M^{\prime}$ 在 $\llbracket \mathrm{t}^{\prime} / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket$ 中。我们可以进一步要求，不妨 $\overline{\mathrm{Y}} \# \operatorname{ftv}\left(M^{\prime \prime}\right)(7)$。现在，让我们在蕴含声明的每一边添加conjunct let $\Gamma_{0} ; \operatorname{ref} M$ in $\llbracket \mu^{\prime \prime}: M^{\prime \prime} \rrbracket$。在左侧，通过C-InAnd和定义1.7.4，我们得到 let $\Gamma_{0}$; ref $M$ in $\llbracket \mathrm{t} / \mu \mu^{\prime \prime}: \mathrm{T} / M M^{\prime \prime} \rrbracket$ (8)。在右侧，通过(5)，(7)，C-ExAnd和C-InAnd，我们得到 $\exists \overline{\mathrm{Y}}$。let $\Gamma_{0}$ in (let ref $M^{\prime}$ in $\llbracket \mathrm{t}^{\prime} / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket \wedge$ let ref $M$ in $\left.\llbracket \mu^{\prime \prime}: M^{\prime \prime} \rrbracket\right)$ (9)。现在，回想一下 $M^{\prime}$ 扩展 $M$ (6) 并且，此外，(3) 意味着 $f p i\left(\llbracket \mu^{\prime \prime}\right.$ : $\left.M^{\prime \prime}\right)$ \# $d p i\left(M^{\prime} \backslash M\right)$ (10)。通过(10)，C-InAnd*和C-InAnd，(9) 等价于 $\exists \bar{Y}$.let $\Gamma_{0} ;$ ref $M^{\prime}$ in $\left(\llbracket \mathrm{t}^{\prime} / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket \wedge

子情况 $\mathcal{E}=[]$。假设和目标一致。

子情况 $\mathcal{E}=\mathcal{E}_{1} \mathrm{t}_{1}$. 归纳假设是 $\mathcal{E}_{1}[\mathrm{t}] / \mu \sqsubseteq \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}$ (1)。让我们引入一个类型 $\mathrm{T}$ 和一个存储类型 $M$ 使得 $\operatorname{dom}(M)=\operatorname{dom}(\mu)$。考虑约束 let $\Gamma_{0} ; \operatorname{ref} M$ 在 $\llbracket \mathcal{E}[\mathrm{t}] / \mu: \mathrm{T} / M \rrbracket$(2)。根据约束生成的定义，C-ExAnd，C-InEx，和C-InAnd，它等价于

## 存在X。（令 $\Gamma_{0} ; \operatorname{ref} M$ 在 $\llbracket \mathcal{E}_{1}[\mathrm{t}] / \mu: \mathrm{X} \rightarrow \mathrm{T} / M \rrbracket$ 中且令 $\Gamma_{0} ; \operatorname{ref} M$ 在 $\left.\llbracket \mathrm{t}_{1}: \mathrm{X} \rrbracket\right)(\mathbf{3})$ 中）

在哪里，$\mathrm{X}$ 不属于 $ftv(\mathrm{T}, M)$ (4)。根据 (1)，存在类型变量 $\overline{\mathrm{Y}}$ 和一个存储类型 $M^{\prime}$ 使得 $\overline{\mathrm{Y}}$ 与 $ftv(\mathrm{X}, \mathrm{T}, M)$ 不相干 (5) 且 $ftv(M^{\prime})$ 是 $\overline{\mathrm{Y}} \cup ftv(M)$ 的子集 (6) 且 $\operatorname{dom}(M^{\prime}) = \operatorname{dom}(\mu^{\prime})$，$M^{\prime}$ 扩展了 $M$ 并且 (3) 包含。

$$
\exists \mathrm{X} .\left(\exists \overline{\mathrm{Y}} . \text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}: \mathrm{X} \rightarrow \mathrm{T} / M^{\prime} \rrbracket \wedge \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket \mathrm{t}_{1}: \mathrm{X} \rrbracket\right)(7)
$$

我们之前指出，在$t_{1}$中出现的看似自由的内存位置是$\operatorname{dom}(M)$的成员，这意味着 let ref $M$ in $\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket$ 等价于 let ref $M^{\prime}$ in $\llbracket \mathrm{t}_{1}$ :。

由（5）可知，C-ExAnd，（8），C-InAnd，以及根据约束生成的定义，我们发现（7）等价于
```plaintext
由（5）可得 C-ExAnd，（8），C-InAnd，并根据约束生成的定义，我们得出（7）等价于
```

$$
\exists \mathrm{x} \bar{Y} \text {.let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in }\left(\llbracket \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right]: \mathrm{X} \rightarrow \mathrm{T} \rrbracket \wedge \llbracket \mathrm{t}_{1}: \mathrm{X} \rrbracket \wedge \llbracket \mu^{\prime}: M^{\prime} \rrbracket\right)(\mathbf{9}) \text {. }
$$

(4)、(5)和(6)意味着 $\mathrm{X} \notin f t v\left(M^{\prime}\right)$。因此，根据C-InEx和C-ExAnd，(9)可以写成


$$
\exists \overline{\mathrm{Y}} \text {.let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in }\left(\exists \mathrm{x} .\left(\llbracket \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right]: \mathrm{X} \rightarrow \mathrm{T} \rrbracket \wedge \llbracket \mathrm{t}_{1}: \mathrm{X} \rrbracket\right) \wedge \llbracket \mu^{\prime}: M^{\prime} \rrbracket\right) \text {, }
$$

根据约束生成的定义，它是

$$
\exists \bar{Y} \text {.let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket \mathcal{E}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket(\mathbf{1 0}) \text {. }
$$

因此，我们已经证明了(2)蕴含(10)。根据定义1.7.5，这确立了 $\mathcal{E}[\mathrm{t}] / \mu \sqsubseteq \mathcal{E}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}$。

子情况 $\mathcal{E}=\mathrm{v} \mathcal{E}_{1}$. 类似于前一个子情况。

子情况 $\mathcal{E}=$ 让 $\mathrm{z}=\mathcal{E}_{1}$ 在 $\mathrm{t}_{1}$ 中。归纳假设是 $\mathcal{E}_{1}[\mathrm{t}] / \mu \sqsubseteq$ $\mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}(\mathbf{1})$。这个子情况特别有趣，因为它是让多态和副作用相互作用的地方。在前面两个子情况中，我们依赖于 $\exists \bar{Y}$ 量词，它隐藏了由归约步骤创建的内存单元的类型，与由应用上下文引入的连接词 $\exists$ 和 $\wedge$ 可交换。然而，一般来说，它不（左）与 let 连接词交换（示例 1.3.28）。幸运的是，在值限制下，这个子情况永远不会出现（引理 1.7.8）。根据定义 1.7.7，只有当所有常数都具有纯语义时，这个子情况才可能发生，这意味着 $\mu=\mu^{\prime}=\varnothing$。然后，我们有

$$
\begin{align*}
& \text { let } \Gamma_{0} \text { in } \llbracket \mathcal{E}[\mathrm{t}]: \mathrm{T} \rrbracket \\
= & \text { let } \Gamma_{0} ; \mathrm{z}: \forall \mathrm{X}\left[\llbracket \mathcal{E}_{1}[\mathrm{t}]: \mathrm{X} \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket  \tag{2}\\
\equiv & \text { let } \Gamma_{0} ; \mathrm{z}: \forall \mathrm{X}\left[\text { let } \Gamma_{0} \text { in } \llbracket \mathcal{E}_{1}[\mathrm{t}]: \mathrm{x} \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket  \tag{3}\\
\Vdash & \text { let } \Gamma_{0} ; \mathrm{z}: \forall \mathrm{X}\left[\text { let } \Gamma_{0} \text { in } \llbracket \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right]: \mathrm{X} \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket  \tag{4}\\
\equiv & \text { let } \Gamma_{0} \text { in } \llbracket \mathcal{E}\left[\mathrm{t}^{\prime}\right]: \mathrm{T} \rrbracket \tag{5}
\end{align*}
$$

其中（2）是根据约束生成的定义；（3）根据 $f t v\left(\Gamma_{0}\right)=$ $f p i\left(\Gamma_{0}\right)=\varnothing$ 和 C-LETDup 而得；（4）是从（1）推演而来，专门针对纯语义的情况；而（5）则是通过逆向执行这些步骤而获得的。

1.7.10 练习（推荐，三星级）：尝试在非纯语义情况下，且在没有值限制的情况下执行上述证明的最后一个小案例。找出它为何失败。证明如果假设 $\bar{Y}$ 为空，它会成功。利用这个事实来证明，只要将泛化限制在非扩张表达式上，泛化仍然是安全的，条件是：（i）计算一个非扩张表达式不能导致新的内存单元被分配，（ii）非扩张表达式通过值替换变量是稳定的，以及（iii）非扩张表达式通过约简保持不变。

主题减少确保了类型良好的性质通过减少得到保持。

1.7.11 引理：设 $t / \mu \longrightarrow t^{\prime} / \mu^{\prime}$。如果 $t / \mu$ 类型良好，那么 $t^{\prime} / \mu^{\prime}$ 也是类型良好的。

证明：假设 $t / \mu \longrightarrow t^{\prime} / \mu^{\prime}$ （1）且 $t / \mu$ 是类型正确的（2）。由（2）和定义1.7.4，存在一个类型 $\mathrm{T}$ 和一个存储类型 $M$ 使得 $\operatorname{dom}(\mu) = \operatorname{dom}(M)$ 并且约束 let $\Gamma_{0} ; \operatorname{ref} M$ in $\llbracket \mathrm{t} / \mu: \mathrm{T} / M \rrbracket$ （3）是可满足的。由定理1.7.9和定义1.7.5，（1）意味着存在一组类型变量 $\overline{\mathrm{Y}}$ 和一个存储类型 $M^{\prime}$ 使得 $\operatorname{dom}\left(M^{\prime}\right) = \operatorname{dom}\left(\mu^{\prime}\right)$ （4）且约束（3）蕴含 $\exists \overline{\mathrm{Y}}$. let $\Gamma_{0}$; ref $M^{\prime}$ in $\llbracket \mathrm{t}^{\prime} / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket$ （5）。因为（3）是可满足的，所以（5）也是可满足的，这意味着 let $\Gamma_{0}$; ref $M^{\prime}$ in $\llbracket \mathrm{t}^{\prime} / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket$ 是可满足的（6）。由（4）和（6）及定义1.7.4，$t^{\prime} / \mu^{\prime}$ 是类型正确的。

让我们现在建立进度属性。

1.7.12 引理：如果 $t_{1} t_{2}$ 类型正确，那么 $t_{1} / \mu$ 和 $t_{2} / \mu$ 也是类型正确的。如果令 $z=$ $t_{1}$ 在 $t_{2} / \mu$ 中是类型正确的，那么 $t_{1} / \mu$ 也是类型正确的。

1.7.13 定理 [进展]：如果 $t / \mu$ 类型正确，那么要么它是可还原的，要么 $t$ 是一个值。

证明：通过归纳$t$的结构进行证明。

- 情况 $\mathrm{t}=\mathrm{z}$。良好类型的配置是封闭的：这种情况不可能发生。
- 情况 $\mathrm{t}=m$。$\mathrm{t}$ 是一个值。
- 情况 $\mathrm{t}=\mathrm{c}$。根据定义1.7.6的要求（ii）。

病例 $\mathrm{t}=\lambda$ z.t $\mathrm{t}_{1} . \mathrm{t}$ 是一个值。

- 情况 $\mathrm{t}=\mathrm{t}_{1} \mathrm{t}_{2}$。根据引理1.7.12，$\mathrm{t}_{1} / \mu$ 是类型良好的。根据归纳假设，要么它是可约的，要么 $\mathrm{t}_{1}$ 是一个值。如果是前者，由于 $\mathrm{R}$-CONTEXT 以及任何形如 $\mathcal{E} t_{2}$ 的上下文都是求值上下文，配置 $t / \mu$ 也是可约的。因此，让我们假设 $t_{1}$ 是一个值。根据引理1.7.12，$\mathrm{t}_{2} / \mu$ 是类型良好的。根据归纳假设，要么它是可约的，要么 $t_{2}$ 是一个值。如果是前者，由于 $\mathrm{R}$-CONTEXT 以及任何形如 $t_{1} \mathcal{E}$ ——其中 $t_{1}$ 是一个值——的上下文都是求值上下文，配置 $t / \mu$ 也是可约的。因此，让我们假设 $t_{2}$ 是一个值。现在让我们根据 $t_{1}$ 的结构进行分类讨论。

子情况 $\mathrm{t}_{1}=\mathrm{z}$。同样，这种子情况不可能发生。

子情况 $t_{1}=m$。因为 $t / \mu$ 类型良好，必须满足形式的约束 let $\Gamma_{0}$; ref $M$ in $\left(\exists x .(m \preceq X \rightarrow T \wedge \llbracket t_{2}: x \rrbracket) \wedge \llbracket \mu: M \rrbracket\right)$。这意味着 $m$ 是 $\operatorname{dom}(M)$ 的成员，并且约束
ref $M(m) \leq X \rightarrow T$ 是可以满足的。因为类型构造器 ref 和 $\rightarrow$ 不兼容，这是矛盾的。所以，这个子情况不可能发生。

子情况 $t_{1}=\lambda z t_{1}^{\prime}$. 根据R-BETA，$t / \mu$ 是可约的。

子情况 $\mathrm{t}_{1}=\mathrm{cv}_{1} \ldots \mathrm{v}_{k}$. 然后，$\mathrm{t}$ 的形式为 $\mathrm{c}_{1} \ldots \mathrm{v}_{k+1}$. 结果根据定义1.7.6的要求（ii）得出。

- 情况 $\mathrm{t}=$ 让 $\mathrm{z}=\mathrm{t}_{1}$ 在 $\mathrm{t}_{2}$ 中。根据引理1.7.12，$\mathrm{t}_{1} / \mu$ 是类型正确的。根据归纳假设，要么 $t_{1} / \mu$ 可约，要么 $t_{1}$ 是一个值。如果是前者，由于 $\mathrm{R}$-上下文以及每个形如 let $\mathrm{z}=\mathcal{E}$ in $\mathrm{t}_{2}$ 的上下文都是求值上下文，配置 $t / \mu$ 也是可约的。如果是后者，那么 $t / \mu$ 通过 $\mathrm{R}$-LET 也是可约的。

我们可能现在可以得出结论：

1.7.14 定理 [类型安全]：类型正确的源程序不会出错。

证明：我们说一个源程序$t$是类型良好的当且仅当配置$t / \varnothing$是类型良好的，也就是说，当且仅当存在$\mathrm{X}$使得$\Gamma_{0}$中的$\llbracket t: \mathrm{x} \rrbracket \equiv$真成立。根据引理1.7.11，$t / \varnothing$的所有约简都是类型良好的。根据定理1.7.13，没有一个会陷入停滞。

让我们回想一下，这个结果仅在满足定义1.7.6的要求时才成立。换句话说，当给出$\mathcal{Q}, \xrightarrow{\delta}$ 和 $\Gamma_{0}$的具体定义时，还需要完成一些证明义务。下一节将通过几个例子来说明这一点。

### 1.8 约束求解

我们引入了一种参数化的约束语言，给出了描述其逻辑连接词之间交互作用的等价定律，并利用它们来证明关于类型推断和类型安全性的定理，这些定理独立于原始约束的性质——所谓谓词应用。然而，提出一个参数化的约束求解器意义不大，因为设计高效约束求解器的困难之处很大程度上在于处理原始约束及其与let多态性的交互。因此，在本节中，我们关注在仅限等式的自由树模型设置下的约束求解。因此，这里开发的约束求解器可以执行$\mathrm{HM}(=)$（即，为Damas和Milner的类型系统）以及带有递归类型扩展的类型推断。当然，其中一些机制可能在其他设置中也有用。程序分析或类型推断中使用的其他约束求解器在例如（Aiken和Wimmers，1992；Niehren）中有所描述。

穆勒，波德尔斯基，1997年；法恩德里希，1999年；梅尔斯基和雷普斯，2000年；穆勒，尼伦，特雷因，2001年；波蒂耶，2001年b；尼尔森，尼尔森，塞德尔，2002年；麦克阿勒斯特，2002年，2003年）。

我们从一个基于规则的标准、高效的一阶统一算法的展示开始。这产生了一个约束求解器，用于一个约束语言的子集，这个子集去掉了类型方案引入和实例化形式。在此基础上，我们构建了一个完整的约束求解器，它对应于伴随本章的代码。

## Unification

统一是解决项之间方程的过程。我们现在呈现一个由Huet（1976）提出的统一算法，作为一个（非确定性）约束重写规则系统。在有限和正规树模型的情况下，规范几乎相同：在后一种情况下，只需移除实现出现检查的一个规则。换句话说，该算法可以处理可能带有循环的项，并且本质上不依赖于出现检查。为了准确反映实际算法的行为，该算法依赖于联合查找数据结构（Tarjan，1975），我们通过将等式替换为多元等式来修改约束的语法。多元等式是一个涉及任意数量的类型的等式，而不是恰好两个。

1.8.1 定义：对于每种类型 $\kappa$ 和每个 $n \geq 1$，存在一个谓词 ${ }_{\kappa}^{n}$，其签名是 $\kappa^{n} \Rightarrow \cdot$，其解释是（$n$ 元）相等性。谓词约束 $={ }_{\kappa}^{n} \mathrm{~T}_{1} \ldots \mathrm{T}_{n}$ 写作 $\mathrm{T}_{1}=\ldots=\mathrm{T}_{n}$，称为多元方程。我们将长度为 0 的多元方程视为真。以下，我们将多元方程按其成员的排列进行识别，因此，类型为 $\kappa$ 的多元方程 $\epsilon$ 可以被视为类型为 $\kappa$ 的有限多重集合。我们写作 $\epsilon=\epsilon^{\prime}$ 表示通过连接 $\epsilon$ 和 $\epsilon^{\prime}$ 而得到的多元方程。

因此，我们对约束语言以下子集感兴趣：

$$
U::=\text { true } \mid \text { false }|\epsilon| U \wedge U \mid \exists \overline{\mathrm{X}} . U
$$

方程被替换为多方程；没有其他谓词可用。类型方案引入和实例化形式不存在。

1.8.2 定义：一个多方程是标准的，当且仅当其变量成员是不同的，并且它最多只有一个非变量成员。一个约束$U$是标准的，当且仅当$U$内的每个多方程都是标准的，且在$U$中出现（自由或约束）的每个变量最多是$U$内一个多方程的成员。

联合查找算法维护变量的一致性类（即不相交的集合），并为每个类关联一个描述符，在我们的情况下，描述符要么不存在，要么是一个非变量项。因此，一个标准约束表示联合查找算法的状态。一个非标准的约束可以看作是联合查找算法状态和控制信息的叠加。例如，形如 $\epsilon=\mathrm{T}_{1}=\mathrm{T}_{2}$ 的多方程，其中 $\mathrm{T}_{1}$ 和 $\mathrm{T}_{2}$ 是非变量项，大致可以看作是等价类 $\epsilon=\mathrm{T}_{1}$，以及一个待处理的请求，解决 $\mathrm{T}_{1}=\mathrm{T}_{2}$ 并相应地更新类的描述符。因为多方程编码了状态和控制，我们对于统一的规格说明相当高阶。可能给出一个低级描述，其中状态（多方程的标准连接）和控制（待处理的二元方程）是区分开的。

1.8.3 定义：令$U$为多个方程的合取。若$U$中包含形如$\mathrm{X}=F \overrightarrow{\mathrm{T}}=\epsilon$的合取，其中$\mathrm{Y} \in f t v(\overline{\mathrm{T}})$，则称$\mathrm{Y}$在$U$关系下被$\mathrm{X}$支配（记作：$\mathrm{Y} \prec_{U} \mathrm{X}$）。$U$是循环的，当且仅当$\prec_{U}$的图表现出一个循环。

统一算法的规范由一组约束重写规则组成，如图1-11所示。重写是在考虑到$\alpha$-转换、多方程成员的排列、连词的交换性和结合性的情况下进行的，并且可以在任意上下文中进行。该规范是非确定性的：可能有几个规则实例同时适用。

S-ExAnd是C-ExAnd的有向版本，其作用是提升所有的存在量词。在这个过程中，所有的多方程都变成了单个合取的一部分，这可能导致左端是多个方程合取的规则，即S-FUSE和S-CYCLE变得适用。S-FUSE识别两个共享公共变量X的多方程并将它们融合。新的多方程不一定标准，即使两个原始多方程是标准的。实际上，它可能含有重复的变量或包含两个非变量项。接下来几条规则的目的是处理这些情况，这些规则的左端只包含一个多方程。S-STUTTER消除冗余变量。它只处理变量，而不是任意大小的项，以使耗时恒定。非变量项的比较是通过S-DECOMPOSE和SClash实现的。S-Decompose分解两个头部符号匹配的项之间的方程。它生成它们子项之间的方程合取，即X向量=T向量。两个项中只有一个保留在原始多方程中，这样原始多方程可能变为标准。项X向量被复制——右侧有两个X向量的出现。因此，我们……（此处原文未提供完整句子，故翻译亦无法提供完整句意）。

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

## 图1-11：统一性

要求它们是类型变量，而不是任意大小的项。（我们通过使用$\overrightarrow{\mathrm{x}}$来表示一个类型变量向量，其元素不一定是唯一的，从而稍微滥用了一下表示法。）这样做，我们允许显式地推理共享：由于变量代表一个等价类的指针，我们明确指出只有指针被复制，而不是整个项。由于这个决定，当两个项中都有非变量子项时，$\mathrm{S}$-DECOMPOSE就无法适用。S-NAME-1通过引入一个代表这样一个子项的新变量来纠正这个问题。当反复应用S-NAME-1时，得到的是一个由所谓的小项组成的统一问题 - 也就是说，共享已经被完全显式化。S-CLASH通过处理两个具有不同头部符号的项相等的情况来补充S-DECOMPOSE；在一个自由树模型中，这样的等式是错误的，因此会发出失败信号。S-SingLE和S-TRUE分别抑制大小为1和0的多方程，这些多方程是同义反复。S-SINGLE仅限于非变量项，以免破坏每个变量恰好是其中一个多方程成员的性质（定义1.8.2）。S-CYCLE是循环检查：也就是说，如果约束是循环的，它会发出失败信号。它仅在语法统一的情况下适用，即当地面类型是有限树时。它是一个全局检查：它的左侧是一个多方程的整个合取。

S-FAIL传播失败；$\mathcal{U}$ 范围涵盖统一约束上下文。

图1-11中的约束重写系统具有以下性质。首先，重写是强规范化的，因此这些规则定义了一个（非确定性）算法。其次，重写是保持意义的。第三，每个规范形式要么是假的，要么是形如 $\exists \overline{\mathrm{X}} . U$ 的形式，其中 $U$ 是可满足的。后两个性质表明该算法确实是一个约束求解器。

1.8.4 引理：重写系统 → 是强归约的。

1.8.5 引理：$U_{1} \rightarrow U_{2}$ 意味着 $U_{1} \equiv U_{2}$。

1.8.6 引理：每个范式要么是假的，要么是形如 $\mathcal{X}[U]$ 的形式，其中 $\mathcal{X}$ 是一个存在量词约束上下文，$U$ 是多方程的标准合取，如果模型是句法的，$U$ 是非循环的。这些条件意味着 $U$ 是可满足的。

## 一个约束求解器

在统一算法的基础上，我们现在定义了一个约束求解器。它的规格独立于统一算法所采用的规则和策略。然而，在执行泛化时，即创建和简化类型方案时，会利用统一算法正常形式的结构以及多方程的逻辑属性。与统一算法一样，约束求解器也是根据一个缩减系统来指定的。但是，需要进行重写的对象不仅仅是约束：它们具有更复杂的结构。处理这种更丰富的状态允许我们区分求解器的外部语言——即完整的约束语言，用于表达人们希望解决的问题——以及下面介绍的内部语言，用于描述求解器的私有数据结构。以下内容中，$C$ 和 $D$ 范围为外部约束，即作为求解器输入部分的约束。外部约束被视为抽象语法树，除了 $\alpha$-转换之外，不受任何隐含法则的约束。作为一个简化的假设，我们要求外部约束不包含任何假的表达式——否则手头上的问题显然是假的。内部数据结构包括前面研究过的统一约束$U$以及栈。栈是第24页定义的约束上下文的一个子集。它们的语法如下：

$$
S::=\square|S[[] \wedge C]| S[\exists \overline{\mathrm{x}} .[]] \mid S[\text { let } \mathrm{x}: \forall \overline{\mathrm{x}}[[]] . \mathrm{T} \text { in } C] \mid S[\text { let } \mathrm{x}: \sigma \text { in []] }
$$

在第二个和第四个生成中，$C$ 是一个外部约束。在最后一个生成中，我们要求 $\sigma$ 具有形如 $\forall \overline{\mathrm{X}}[U]X$ 的形式，并且我们要求 $\exists \sigma \equiv$ 真实。堆栈可以被视为帧的列表。帧可以在堆栈内部的末端添加和删除，即靠近它表示的约束上下文的孔。我们分别将四种帧称为连词、存在、let和环境帧。约束求解器的状态是一个三元组 $S ; U ; C$，其中 $S$ 是一个堆栈，$U$ 是一个统一约束，$C$ 是一个外部约束。状态 $S ; U ; C$ 应被理解为约束 $S[U \wedge C]$ 的表示。据此定义了状态之间的 $\alpha$-等价性。特别地，可以在 $d t v(S)$ 中重命名类型变量，前提是 $U$ 和 $C$ 也被重命名。简而言之，状态的三部分扮演以下角色。$C$ 是求解器打算接下来检查的外部约束。$U$ 是底层统一算法的内部状态：可以将其视为到目前为止已获得的知识。$S$ 告诉在 $U$ 和 $C$ 中自由出现的类型变量在哪里绑定，将类型方案与在 $C$ 中自由出现的程序变量关联起来，并记录在解决 $C$ 之后应该做什么。求解器的初始状态通常是 []; true; $C$ 的形式，其中 $C$ 是人们希望解决的的外部约束，即其可满足性人们希望确定。为了简单起见，我们做出了（非本质的）假设，即状态没有自由类型变量。

求解器由一个（非确定性的）状态重写系统组成，如图1-12所示。重写是在模 $\alpha$-转换的情况下进行的。S-UNIFY将统一算法作为约束求解器的一个组件，并允许当前的统一问题$U$随时被解决。规则S-Ex-1至SEx-4将存在量词从统一问题中提取出来，放到栈中，如果存在的话，通过栈传递到最近的封闭let框架，否则放到最外层。它们的副作用条件防止了类型变量的捕获，并且总是可以通过对左手状态进行适当的$\alpha$-转换来满足。如果$S ; U ; C$相对于上述五条规则是正常形式，那么在$d t v(S)$中的每个类型变量要么在let框架中普遍量化，要么在最外层存在性地绑定。（回想一下，根据假设，状态没有自由类型变量。）换句话说，只要这些规则以急切的方式应用，机器表示中的栈就不需要出现存在性框架。相反，只需在每个let框架和最外层维护一个列表，列出在此处绑定的类型变量；反之，在$d t v(S)$中的每个类型变量上注上一个整数等级，这样可以在常数时间内判断变量绑定在何处：等级为0的类型变量在最外层绑定，等级为$k \geq 1$的类型变量在栈$S$中向下第$k^{\text {th }}$个let框架处绑定。本章附带的代码采用了这个约定。等级曾是

| $S ; U ; C$ | $\rightarrow$ | $S ; U^{\prime} ; C$ <br> if $U \rightarrow U^{\prime}$ | (S-UNIFY) |
| :---: | :---: | :---: | :---: |
| $S ; \exists \overline{\mathrm{x}} . U ; C$ | $\rightarrow$ | $S[\exists \overline{\mathrm{X}} .[]] ; U ; C$ <br> if $\overline{\mathrm{x}} \# \operatorname{ftv}(C)$ | $(\mathrm{S}-\mathrm{Ex}-1)$ |
| $S[(\exists \overline{\mathrm{x}} \cdot \square) \wedge C]$ | $\rightarrow$ | $S[\exists \overline{\mathrm{X}} .(\square \wedge C)]$ <br> if $\overline{\mathrm{x}} \# \operatorname{ftv}(C)$ | $(\mathrm{S}-\mathrm{Ex}-2)$ |
| $S[$ let x : $\forall \overline{\mathrm{X}}[\exists \overline{\mathrm{Y}} .[]] . \mathrm{T}$ in $C]$ | $\rightarrow$ | $S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}} \overline{\mathrm{Y}}[[]] \cdot \mathrm{T}$ in $C]$ <br> if $\overline{\mathrm{Y}} \# \operatorname{ftv}(\mathrm{T})$ | $(\mathrm{S}-\mathrm{Ex}-3)$ |
| $S[$ let $\mathrm{x}: \sigma$ in $\exists \overline{\mathrm{x}} .[]]$ | $\rightarrow$ | $S[\exists \overline{\mathrm{X}}$.let $\mathrm{x}: \sigma$ in []$]$ <br> if $\overline{\mathrm{x}} \# \operatorname{ftv}(\sigma)$ | $(\mathrm{S}-\mathrm{Ex}-4)$ |
| $S ; U ; \mathrm{T}_{1}=\mathrm{T}_{2}$ | $\rightarrow$ | $S ; U \wedge \mathrm{T}_{1}=\mathrm{T}_{2} ;$ true | (S-SolvE-EQ) |
| $S ; U ; \mathrm{x} \preceq \mathrm{T}$ | $\rightarrow$ | $S ; U ; S(\mathrm{x}) \preceq \mathrm{T}$ | (S-SoLVE-ID) |
| $S ; U ; C_{1} \wedge C_{2}$ | $\rightarrow$ | $S\left[[] \wedge C_{2}\right] ; U ; C_{1}$ | (S-SolvE-And) |
| $S ; U ; \exists \overline{\mathrm{X}} . C$ | $\rightarrow$ | $S[\exists \overline{\mathrm{X}} .[]] ; U ; C$ <br> if $\overline{\mathrm{x}} \# \operatorname{ftv}(U)$ | (S-SOLVE-Ex) |
| $S ; U ;$ let $\mathrm{x}: \forall \overline{\mathrm{x}}[D] . \mathrm{T}$ in $C$ | $\rightarrow$ | $S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}}[\mathrm{\square}] . \mathrm{T}$ in $C] ; U ; D$ <br> if $\overline{\mathrm{x}} \# \operatorname{ftv}(U)$ | (S-SOLVE-LET) |
| $S[\square \wedge C] ; U ;$ true | $\rightarrow$ | $S ; U ; C$ | (S-POP-AND) |
| $S[$ let $\mathrm{x}: \forall \overline{\mathrm{x}}[\mathrm{[]}] \mathrm{T}$ in $C] ; U$; true | $\rightarrow$ | $S[$ let $\mathrm{x}: \forall \overline{\mathrm{x}} \mathrm{X}[[]] \mathrm{X}$ in $C]$ <br> $U \wedge \mathrm{X}=\mathrm{T} ;$ true <br> if $\mathrm{x} \notin \operatorname{ftv}(U, \mathrm{~T}) \wedge \mathrm{T} \notin \mathcal{V}$ | $(\mathrm{S}-\mathrm{NAME}-2)$ |
| $S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}} \mathrm{Y}[[]] . \mathrm{X}$ in $C] ; \mathrm{Y}=\mathrm{Z}=\epsilon \wedge U$; true | $\rightarrow$ | $S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}} \mathrm{Y}[[]] . \theta(\mathrm{X})$ in $C]$ <br> $\mathrm{Y} \wedge \mathrm{Z}=\theta(\epsilon) \wedge \theta(U) ;$ true <br> if $\mathrm{Y} \neq \mathrm{Z} \wedge \theta=[\mathrm{Y} \mapsto \mathrm{Z}]$ | (S-COMpREss) |
| $S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}} \mathrm{Y}[\mathrm{[}] . \mathrm{X}$ in $C] ; \mathrm{Y}=\epsilon \wedge U$; true | $\rightarrow$ | $S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}}[\mathrm{]}] \cdot \mathrm{X}$ in $C] ; \epsilon \wedge U$; true <br> if $\mathrm{Y} \notin \mathrm{x} \cup \operatorname{ftv}(\epsilon, U)$ | (S-UnNAME) |
| $S[$ let $\mathrm{x}: \forall \overline{\mathrm{X}} \overline{\mathrm{Y}}[[]] . \mathrm{X}$ in $C] ; U ;$ true | $\rightarrow$ | $S[\exists \overline{\mathrm{Y}}$.let $\mathrm{x}: \forall \overline{\mathrm{X}}[\square] . \mathrm{X}$ in $C] ; U ;$ true <br> if $\overline{\mathrm{Y}} \# \operatorname{ftv}(C) \wedge \exists \overline{\mathrm{X}} . U$ determines $\overline{\mathrm{Y}}$ | (S-LETALL) |
| $S[$ let x : $\forall \overline{\mathrm{x}}[[]] . \mathrm{x}$ in $C] ; U_{1} \wedge U_{2} ;$ true | $\rightarrow$ | $S\left[\right.$ let x : $\forall \overline{\mathrm{x}}\left[U_{2}\right] \cdot \mathrm{X}$ in $\left.\square\right] ; U_{1} ; C$ <br> if $\overline{\mathrm{x}} \# \operatorname{ftv}\left(U_{1}\right) \wedge \exists \overline{\mathrm{x}} \cdot U_{2} \equiv$ true | (S-POP-LET) |
| $S[$ let $\mathrm{x}: \sigma$ in []$] ; U$; true | $\rightarrow$ | $S ; U ;$ true | (S-Pop-Env) |

图1-12：一个约束求解器最初在（Rémy，1992a）中描述，也出现在（McAllester，2003）中。

规则 S-Solve-EQ 到 S-SoLVE-LET 编码了对当前状态第三组件结构的分析。除虚假情况外，每种可能的情况都有一条规则，按假设虚假情况不会出现，而真实情况将在后面处理。S-SolvE-EQ 发现一个方程并将其提供给统一算法。S-SOLVE-ID 发现一个实例化约束 x ≼ T 并用 σ ≼ T 替换它，其中类型方案 σ=S(x) 是在堆栈 S 中定义 x 的最近环境框架所携带的类型方案。它的定义如下：

$$
\begin{aligned}
& S[[] \wedge C](\mathrm{x})=S(\mathrm{x}) \\
& S[\exists \overline{\mathrm{x}} . \square](\mathrm{x})=S(\mathrm{x}) \text { if } \overline{\mathrm{x}} \# \operatorname{ftv}(S(\mathrm{x})) \\
& S[\text { let y }: \forall \overline{\mathrm{x}}[\mathrm{\square}] . \mathrm{T} \text { in } C](\mathrm{x})=S(\mathrm{x}) \text { if } \overline{\mathrm{x}} \# \operatorname{ftv}(S(\mathrm{x})) \\
& S[\text { let } \mathrm{y}: \sigma \text { in } \square](\mathrm{x})=S(\mathrm{x}) \text { if } \mathrm{x} \neq \mathrm{y} \\
& S[\text { let } \mathrm{x}: \sigma \text { in } \square](\mathrm{x})=\sigma
\end{aligned}
$$

如果 $\mathrm{x} \in d p i(S)$ 不成立，那么 $S(\mathrm{x})$ 是未定义的，规则不适用。如果成立，那么通过适当转换左手状态的 $\alpha$-转换，规则可能总是适用。请记住，如果 $\sigma$ 是形如 $\forall \overline{\mathrm{X}}[U] . \mathrm{X}$ 的形式，其中 $\overline{\mathrm{X}} \# \operatorname{ftv}(\mathrm{T})$，那么 $\sigma \preceq \mathrm{T}$ 表示 $\exists \overline{\mathrm{X}} .(U \wedge \mathrm{X}=\mathrm{T})$。构建此约束的过程非正式地称为“取 $\sigma$ 的一个实例”。它涉及取类型变量 $\overline{\mathrm{X}}$，合一约束 $U$ 和主体 $\mathrm{X}$ 的新副本。在最坏的情况下，这个过程与在程序源代码中逐字展开相应的 let 构造一样低效，并且会导致指数时间复杂度（Mairson, Kanellakis 和 Mitchell, 1991年）。然而，在实际中，合一约束 $U$ 通常很紧凑，因为它在创建环境框架 let $\mathrm{x}: \sigma$ in [] 之前被简化了，这就是求解器通常表现良好的原因。（由 S-POP-LET 执行的环境框架创建将在下面讨论。）S-SOLVEAND 发现了一个合取。它任意选择先探索左分支，并将合取框架推入栈中，以便记录随后应探索右分支。S-SOLVE-Ex 发现了一个存在量词并进入其中，创建一个新的存在框架以记录其存在。同样，S-SOLVE-LET 发现了一个 let 形式并进入其左侧，创建一个新的 let 框架以记录其存在。先检查左侧的选择不是任意的。实际上，先检查右侧将需要创建一个环境框架，但环境框架必须包含简化后的类型方案，形式为 $\forall \overline{\mathrm{X}}[U] . \mathrm{X}$，而类型方案 $\forall \overline{\mathrm{X}}[D] . T$ 是任意的。换句话说，我们的策略是在允许它们通过 S-SOLVE-ID 复制之前简化类型方案，以避免任何重复工作。S-SOLVE-Ex 和 S-SOLVE-LET 的附加条件总是可以通过适当转换左手状态来满足。

S-Solve-EQ到S-Solve-LET的规则可以被称为前向规则，因为它们“深入”到外部约束中，导致堆栈增长。当当前的外部约束变为真时，这个过程停止。这时，部分工作已经完成，求解器必须检查堆栈以确定下一步该做什么。这一任务由最后一系列规则执行，这些规则可以被称为后向规则，因为它们“退回出来”，导致堆栈缩小，并可能安排新的外部约束进行检查。这些规则编码了对最内层堆栈帧结构的分析。有三种子情况，分别对应于连接、let和环境帧。存在栈帧的情况不需要考虑，因为规则S-Ex-2到S-Ex-4允许将它们与let帧融合，或者将它们浮动到最外层，在那里它们将保持不活动。S-POP-And处理连接帧。该帧被弹出，它携带的外部约束被安排进行检查。S-Pop-Env处理环境帧。由于当前let构造的右侧已经被解决——也就是说，变成了一个统一约束U——它不能包含x的出现。此外，根据假设，∃σ为真。因此，这个环境帧不再有用：它被销毁。剩下的规则处理let帧。粗略地说，它们的目的是将状态S[let x:∀x[[]].T in C];U;true变为S[let x:∀x[U].T in []]$];true;C，即把当前的统一约束U变成一个类型方案，把let帧变成环境帧，并安排let构造的右侧（即外部约束C）进行检查。实际上，这个过程更为复杂，因为类型方案∀x[U].T在成为环境帧的一部分之前必须被简化。简化过程由规则S-NAME-2到S-Pop-LET描述。在以下内容中，我们将∀x中的类型变量称为年轻，将dtv(S)\x中的类型变量称为年老。前者是正在创建的类型方案的全局量词；后者是它的自由类型变量。

S-NAME-2确保正在创建的类型方案中的主体$T$是一个类型变量，而不是任意项。如果不是，则用一个新的变量$\mathrm{X}$替换它，并添加方程$\mathrm{X}=\mathrm{T}$以记住$\mathrm{X}$代表$\mathrm{T}$。这样，规则将项$\mathrm{T}$移动到当前统一问题中，在那里它可能受到S-NAME-1的影响。这确保了共享在所有地方都明确。S-COMPRESS确定（年轻的）类型变量$\mathrm{Y}$是类型变量$\mathrm{Z}$的别名。然后，除了定义出现之外，Y的每个自由出现都被替换为Z。在实际实现中，当联合查找算法执行路径压缩（Tarjan, 1975, 1979）时，这种情况会透明地发生，前提是我们小心不要创建从变量到高级别变量的链接。这需要让统一算法知道等级，但除此之外很容易实现。S-UNNAME确定（年轻的）类型变量Y在当前类型方案中除了定义出现之外没有其他出现。（这发生在特别是S-Compress刚刚应用之后。）然后，$\mathrm{Y}$被完全抑制。在剩余的多方程$\epsilon$的基数为一的特殊情况下，它可以通过S-SingLE被抑制。换句话说，S-UNNAME和S-SINGLE的结合能够抑制年轻的未使用的类型变量以及它们所代表的项。这反过来可能导致新的类型变量被S UNNAME消除的资格。实际上，假设当前的统一约束是无环的，归纳论证表明，除非被$\mathrm{X}$或老类型变量所支配，否则每个年轻的类型变量都可以被抑制。（在正规树模型的背景下，可以扩展规则，使得未被$\mathrm{X}$或老类型变量支配的年轻循环也被抑制。）S-LETALL是C-LETALL的有向版本。它将年轻的类型变量$\overline{\mathrm{Y}}$变成老变量。如何判断$\exists \overline{\mathrm{X}} . U$确定$\overline{\mathrm{Y}}$将在后面讨论（参见引理1.8.7）。为什么S-LETALL是一个有趣且重要的规则将很快解释。S-POP-LET旨在在当前状态关于S-UNIFY、SName-2、S-Compress、S-UnName和S-LetAll达到正常形式时应用，即，即将创建的类型方案完全简化时。它将当前的统一约束分解为两个组件$U_{1}$和$U_{2}$，其中$U_{1}$完全由老变量组成 - 如侧条件$\overline{\mathrm{X}} \# \operatorname{ftv}\left(U_{1}\right)$所表达，而$U_{2}$只约束年轻变量 - 如侧条件$\exists \overline{\mathrm{X}} \cdot U_{2} \equiv$ true所表达。请注意，$U_{2}$可能仍包含老类型变量的自由出现，所以类型方案$\forall \overline{\mathrm{X}}\left[U_{2}\right]$. $\mathrm{X}$在右侧出现不一定闭合。这种分解必须存在的原因尚不明显；引理1.8.11的证明为这个问题提供了更多的启示。现在我们说，S-LETALL在保证其存在方面发挥作用，因此它的重要性部分来自于此。一旦获得分解$U_{1} \wedge U_{2}$，S-POP-LET的行为就很简单了。统一约束$U_{1}$只涉及老变量，即那些在当前let框架中没有量化的变量；因此，它不必成为新类型方案的一部分，而可以保留为当前统一约束的一部分。这由C-LETAnd和C-InAnd*（参见引理1.8.10的证明）证明是合理的，并且与第1.4节中讨论的HMX-GEN'和HMX-GEN之间的区别相对应。另一方面，统一约束$U_{2}$成为新构建的类型方案$\forall \overline{\mathrm{X}}\left[U_{2}\right]$.X的一部分。属性$\exists \overline{\mathrm{X}} . U_{2} \equiv$ true保证了新创建的环境框架符合对这类框架的要求。请注意，被认为是老的类型变量越多，$U_{1}$可能变得越大，而$U_{2}$越小。这是S-LETALL有趣的另一个原因：通过允许更多的变量被认为是老的，它减少了类型方案$\forall \overline{\mathrm{X}}\left[U_{2}\right] . \mathrm{X}$的大小，使其更便宜地获取实例。

为了完整描述约束求解器，还剩下解释何时 $\exists \overline{\mathrm{X}} . U$ 能够确定 $\overline{\mathrm{Y}}$ 的问题，因为这个谓词出现在 S-LETALL 的附加条件中。以下引理描述了两种重要情况，通过检查等式的结构，可以发现约束 $C$ 确定了其中的一些自由类型变量 $\bar{Y}$ （定义1.3.26）。在第一种情况下，类型变量 $\overline{\mathrm{Y}}$ 与 $C$ 中自由出现的不同类型变量 X 相等或被其支配。在这种情况下，因为模型是一个自由树模型，类型变量 $\bar{Y}$ 的值由 $X$ 的值确定——它们是特定位置的其子树。例如，$\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}$ 确定 $\mathrm{Y}_{1} \mathrm{Y}_{2}$，而 $\exists \mathrm{Y}_{1} .\left(\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}\right)$ 确定 $\mathrm{Y}_{2}$。在第二种情况下，类型变量 $\overline{\mathrm{Y}}$ 与一个项 T 相等，T 的所有自由类型变量都在 $C$ 中自由。同样，类型变量 $\overline{\mathrm{Y}}$ 的值然后由类型变量 $f t v(T)$ 的值确定——实际上，项 $\mathrm{T}$ 本身定义了一个将后者映射到前者的函数。例如，$\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}$ 确定 $\mathrm{X}$，而 $\exists \mathrm{Y}_{1}$. $\left(\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}\right)$却不可以。在第二种情况下，实际上并没有关于模型做出任何假设。请注意，$\mathrm{X}=\mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2}$ 确定 $\mathrm{Y}_{1} \mathrm{Y}_{2}$ 同时也确定 $\mathrm{X}$，但不同时确定 $\mathrm{XY}_{1} \mathrm{Y}_{2}$。

1.8.7 引理：设 $\overline{\mathrm{X}} \# \overline{\mathrm{Y}}$。假设要么 $\epsilon$ 是 $\mathrm{X}=\epsilon^{\prime}$，其中 $\mathrm{X} \notin \overline{\mathrm{X}} \overline{\mathrm{Y}}$ 且 $\overline{\mathrm{Y}} \subseteq f t v(\epsilon^{\prime})$，要么 $\epsilon$ 是 $\overline{\mathrm{Y}}=\mathrm{T}=\epsilon^{\prime}$，其中 $\operatorname{ftv}(\mathrm{T}) \# \overline{\mathrm{X}} \overline{\mathrm{Y}}$。那么，$\exists \overline{\mathrm{X}}$。$(C \wedge \epsilon)$ 确定 $\overline{\mathrm{Y}}$。

证明：设 $\overline{\mathrm{X}} \# \overline{\mathrm{Y}}$ (1)。设 $\phi \vdash \operatorname{def} \Gamma$ 在 $\exists \overline{\mathrm{X}}$ 中。$(C \wedge \epsilon)$ (2) 以及 $\phi^{\prime} \vdash$ def $\Gamma$ 在 $\exists \overline{\mathrm{X}}$ 中。$(C \wedge \epsilon)(3)$，其中 $\phi$ 和 $\phi^{\prime}$ 在 $\overline{\mathrm{Y}}$ 外部是一致的。我们可以假设，不失一般性，$\overline{\mathrm{x}} \# \mathrm{ftv}(\Gamma)$ (4)。由(2)，(4)，CM-Exists 和 CM-And，我们得到 $\phi_{1} \vdash \operatorname{def} \Gamma$ 在 $\epsilon(5)$ 中，其中 $\phi$ 和 $\phi_{1}$ 在 $\overline{\mathrm{x}}$ 外部是一致的。根据 CM-Predicate，(5) 意味着 $\epsilon$ 的所有成员通过 $\phi_{1}$ 有相同的像。同样地，利用(3)和(4)，我们发现 $\epsilon$ 的所有成员通过 $\phi_{1}^{\prime}$ 也有相同的像，其中 $\phi^{\prime}$ 和 $\phi_{1}^{\prime}$ 在 $\overline{\mathrm{X}}$ 外部是一致的。现在，我们声称 $\phi_{1}$ 和 $\phi_{1}^{\prime}$ 在 $\overline{\mathrm{Y}}$ 上是一致的。一旦建立这个主张，由(1)可知，$\phi$ 和 $\phi^{\prime}$ 也必须在 $\bar{Y}$ 上是一致的，这正是我们的目标。因此，只剩下证明这一主张；我们区分两种子情况。

子情况 $\epsilon$ 是 $\mathrm{X}=\epsilon^{\prime}$ 且 $\mathrm{X} \notin \overline{\mathrm{X}} \overline{\mathrm{Y}}(\mathbf{6})$ 且 $\overline{\mathrm{Y}} \subseteq f t v\left(\epsilon^{\prime}\right)$ (7)。因为 $\phi_{1}$ 和 $\phi_{1}^{\prime}$ 在 $\overline{\mathrm{X}} \overline{\mathrm{Y}}$ 外部重合，且由（6）可知，我们有 $\phi_{1}(\mathrm{X})=\phi_{1}^{\prime}(\mathrm{X})$。因此，$\epsilon^{\prime}$ 的所有成员通过 $\phi_{1}$ 和 $\phi_{1}^{\prime}$ 有相同的像。在一个自由的树形模型中，分解是有效的，一个简单的归纳论证表明 $\phi_{1}$ 和 $\phi_{1}^{\prime}$ 必须在 $f t v\left(\epsilon^{\prime}\right)$ 上重合，因此 - 由（7）- 也在 $\overline{\mathrm{Y}}$ 上。

子情况 $\epsilon$ 是 $\overline{\mathrm{Y}}=\mathrm{T}=\epsilon^{\prime}$ 且 $f t v(\mathrm{~T}) \# \overline{\mathrm{X}} \overline{\mathrm{Y}}(8)$. 因为 $\phi_{1}$ 和 $\phi_{1}^{\prime}$ 在 $\bar{X} \bar{Y}$ 外部重合，并且由（8），我们有 $\phi_{1}(T)=\phi_{1}^{\prime}(T)$. 因此，对于每个 $Y \in \bar{Y}$，我们有 $\phi_{1}(\mathrm{Y})=\phi_{1}(\mathrm{~T})=\phi_{1}^{\prime}(\mathrm{T})=\phi_{1}^{\prime}(\mathrm{Y})$. 也就是说，$\phi_{1}$ 和 $\phi_{1}^{\prime}$ 在 $\overline{\mathrm{Y}}$ 上重合。

得益于引理1.8.7，我们可以直接实现S-LETALL。问题是，给定一个约束 $\exists \overline{\mathrm{X}} . U$，其中$U$是一组多方程的标准连结，要确定最大的子集$\bar{Y}$，使得$\exists(\overline{\mathrm{X}} \backslash \overline{\mathrm{Y}}) . U$能够确定$\overline{\mathrm{Y}}$。根据引理的第一部分，$\overline{\mathrm{Y}}$可以安全地包括所有直接或间接受某个自由变量（关于$U$）支配的$\overline{\mathrm{X}}$成员。这些可以通过以$U$的大小为线性时间对$\prec_{U}$的图进行自顶向下的遍历来找到。根据引理的第二部分，按照闭包法则$\mathrm{X} \in \overline{\mathrm{X}} \wedge\left(\forall \mathrm{Y} \quad \mathrm{Y} \prec_{U} \mathrm{X} \Rightarrow \mathrm{Y} \in \overline{\mathrm{Y}}\right) \Rightarrow \mathrm{X} \in \overline{\mathrm{Y}}$关闭$\overline{\mathrm{Y}}$是安全的。也就是说，还可以安全地包括所有那些其子孙（关于$U$）已经被发现是$\bar{Y}$成员的$\overline{\mathrm{X}}$成员。这种闭包计算可以通过对$\prec_{U}$的图进行自底向上的遍历再次在线性时间内完成。当$U$是无环时，可以证明这个程序是完整的，即它确实计算出了满足我们要求的最小子集$\bar{Y}$。这是下面练习的主题。

1.8.8练习 $[\star \star \star, \nrightarrow]$ ：假设 $U$ 是无环的，证明以上过程计算的是最大的子集 $\overline{\mathrm{Y}}$ 使得存在 $(\overline{\mathrm{X}} \backslash \overline{\mathrm{Y}}) \cdot U$ 确定 $\overline{\mathrm{Y}}$ 。在正规树模型的设置中，展示一个可满足的约束 $U$ 使得以上过程是不完整的。你能否在该设置中定义一个完整的过程？

上述讨论已经表明，当Y和Z相等时，如果Y年轻而Z年老，那么S-LetAlL允许也使Y变老。如果绑定信息以整数值的等级来编码，正如之前所建议的，那么这个评论可以表述如下：当Y和Z相等时，如果Y的等级超过Z的等级，那么它可以被降低，以便两个等级相匹配。因此，有可能将等级与多方程式关联，而不是与变量关联。当两个多方程式融合时，保留较小的等级。

当将$x$分配给单一类型$T$，而不是任意的类型方案$\forall \overline{X}[D].T$时，S-SOLVE-LET和S-NAME-2到S-POP-LET显得不必要复杂。在这种情况下，可以通过以下两条新规则直接获得这些规则的组合效果，这些规则可以以更高效的方式实现：

$$
\begin{array}{rll}
S ; U ; \text { let } \mathrm{x}: \mathrm{T} \text { in } C \rightarrow & S[\exists \mathrm{x} .[]] ; U \wedge \mathrm{x}=\mathrm{T} \text {; let } \mathrm{x}: \mathrm{x} \text { in } C \\
& & \text { if } \mathrm{x} \notin f t v(U, \mathrm{~T}, C) \wedge \mathrm{T} \notin \mathcal{V} \\
& & \\
S ; U ; \text { let } \mathrm{x}: \mathrm{x} \text { in } C \rightarrow & & S[\text { let } \mathrm{x}: \mathrm{x} \text { in }[]] ; U ; C \quad \text { (S-Solve-LET-Mono) }
\end{array}
$$

如果 $\mathrm{T}$ 不是一个变量，它将被替换为一个新的变量 $\mathrm{X}$，同时伴随方程 $\mathrm{X}=\mathrm{T}$。这对应于 S-NAME-2 的效果。然后，我们直接为 $\mathrm{x}$ 创建一个环境框架，而无需费心创建并丢弃一个 let 框架，因为类型方案 X 不可能进一步简化。

让我们现在陈述并建立约束求解器的特性。首先，归约系统是终结的，因此它定义了一个算法。

1.8.9 引理：约简系统 $\rightarrow$ 是强归约正常的。

其次，每个重写步骤都保留了当前状态所表示的约束的意义。我们回顾一下，状态 $S ; U ; C$ 旨在表示约束 $S[U \wedge C]$。

1.8.10 引理：$S ; U ; C \rightarrow S^{\prime} ; U^{\prime} ; C^{\prime}$ 意味着 $S[U \wedge C] \equiv S^{\prime}[U^{\prime} \wedge C^{\prime}]$.

证明：通过检查每一条规则。

-情形S-Unify。根据引理1.8.5。
-情形S-Ex-1，S-Ex-2，S-Solve-Ex。根据C-ExAnd。
-情形S-Ex-3。根据C-LETEx。
-情形S-Ex-4。根据C-InEx。
-情形S-Solve-Eq，S-Pop-And。根据C-Dup。
-情形S-Solve-ID。因为$\sigma$具有形式$\forall \overline{\mathrm{x}}[U] . \mathrm{X}$，我们有$f p i(\sigma)=\varnothing$。结果遵循C-INID。
-情形S-Solve-And。根据C-AndAnd。
-情形S-Solve-Let。根据C-LetAnd。
-情形S-NAme-2。根据定义1.3.21和C-NAmeEq，$\mathrm{X} \notin f t v(U, \mathrm{~T})$意味着真$\Vdash \forall \overline{\mathrm{X}}[U] . \mathrm{T} \equiv \forall \overline{\mathrm{X}} \mathrm{X}[U \wedge \mathrm{X}=\mathrm{T}] . \mathrm{X}$。结果遵循引理1.3.22。
-情形S-Compress。设$\theta=[\mathrm{Y} \mapsto \mathrm{Z}]$。根据定义1.3.21和CNAMEEQ，$\mathrm{Y} \neq \mathrm{Z}$意味着真$\Vdash \forall \overline{\mathrm{X}}[\mathrm{Y}=\mathrm{Z}=\epsilon \wedge U] . \mathrm{X} \equiv \forall \overline{\mathrm{X}} \mathrm{Y}[\mathrm{Y} \wedge \mathrm{Z}=$ $\theta(\epsilon) \wedge \theta(U)] . \theta(\mathrm{X})$。结果遵循引理1.3.22。
-情形S-UnName。使用引理1.3.18，可以容易地检查$\mathrm{Y} \notin f t v(\epsilon)$意味着$\exists \mathrm{Y}$. $(\mathrm{Y}=\epsilon) \equiv \epsilon$。结果遵循C-ExAnD和C-LETEx。
-情形S-LetAll。根据C-LetAll。
-情形S-Pop-Let。根据C-LetAnd和C-InAnd*。
-情形S-Pop-Env。根据C-IN*，回忆$\exists \sigma$必须是真。

最后，我们对还原系统的范式进行分类：

1.8.11 引理：约简系统 $\rightarrow$ 的一个正规形式是以下之一：(i) $S ; U ; \mathrm{x} \preceq \mathrm{T}$，其中 $\mathrm{x} \notin \text{dpi}(S)$；（ii）$S$；假；真；或者（iii）$\mathcal{X}$；$U$；真，其中 $\mathcal{X}$ 是一个存在量词约束上下文，$U$ 是一个可满足的多方程连结。

证明：由于按照定义，$S ; U$; false 不是一个有效的状态，S-Solve-Eq、S-Solve-Id、S-Solve-And、S-Solve-Ex 和 S-SolveLET 的正规形式必须是 S-SOLVE-ID 左侧实例的形式，且 $\mathrm{x} \notin d p i(S)$，这对应于情况 (i)，或者是 $S$; $U$; true 的形式。让我们考虑后一种情况。因为 $S ; U$; true 关于 S-UNIFY 是一个正规形式，根据引理 1.8.6，$U$ 必须是 false 或 $\mathcal{X}\left[U^{\prime}\right]$ 的形式，其中 $U^{\prime}$ 是多方程的标准联接，如果模型是句法的，$U^{\prime}$ 是非循环的。前者对应于 (ii)；因此，让我们考虑后一种情况。因为 $S ; \mathcal{X}\left[U^{\prime}\right]$; true 关于 $\mathrm{S}$-EX1 是一个正规形式，上下文 $\mathcal{X}$ 实际上必须是空的，而 $U^{\prime}$ 就是 $U$。如果 $S$ 是一个存在约束上下文，那么我们处于情况 (iii)。否则，因为 $S ; U$; true 关于 S-Ex-2、S-Ex-3 和 S-Ex-4 是一个正规形式，堆栈 $S$ 不会以存在帧结束。因为 $S ; U$; true 关于 S-Pop-And 和 S-Pop-Env 是一个正规形式，所以 $S$ 必须是 $S^{\prime}[$ let $\mathrm{x}: \forall \overline{\mathrm{X}}[\mathrm{[I}] \mathrm{T}$ in $C]$ 的形式。因为 $S ; U$; true 关于 S-NAME-2 是一个正规形式，T 必须是一个类型变量 $\mathrm{X}$。让我们将 $U$ 写成 $U_{1} \wedge U_{2}$ 的形式，其中 $\overline{\mathrm{X}} \# \operatorname{ftv}\left(U_{1}\right)$，并且 $U_{1}$ 是满足这一标准的最大项。那么，考虑一个多方程 $\epsilon \in U$。根据引理 1.8.7 的第一部分，如果 $\epsilon$ 中的某个变量成员是自由的（即不在 $\overline{\mathrm{X}}$ 中），那么 $\exists \overline{\mathrm{X}} . U$ 确定了 $f t v(\epsilon)$ 中所有其他变量。因为 $S ; U$; true 关于 S-LETALL 是一个正规形式，$f t v(\epsilon)$ 中的所有变量必须是自由的（即不在 $\overline{\mathrm{X}}$ 中）。根据 $U_{1}$ 的定义，这意味着 $\epsilon \in U_{1}$。通过逆否，对于 $U_{2}$ 中的每个多方程 $\epsilon$，$\epsilon$ 中的所有变量成员都在 $\overline{\mathrm{X}}$ 中。此外，让我们回忆一下 $U_{2}$ 是多方程的标准联接，如果模型是句法的，$U_{2}$ 是非循环的。我们让读者验证这暗示了 $\exists \overline{\mathrm{x}} . U_{2} \equiv$ true；这个证明是引理 1.8.6 最后部分的略微推广。那么，$S ; U$; true 可以通过 S-PoP-LET 进行简化。这是一个矛盾，所以这种情况不可能出现。

在情况（i）中，约束$S[U \wedge C]$有一个自由的程序标识符x，因此它不可满足。换句话说，源程序包含一个未绑定的程序标识符。当然，如果需要，这种错误可以在约束求解之前被检测到。在情况（ii）中，统一算法失败了。根据引理1.3.30，约束$S[U \wedge C]$则为假。在情况（iii）中，约束$S[U \wedge C]$等价于$\mathcal{X}[U]$，其中$U$是可满足的，因此它也是可满足的。因此，这三类正规形式中的每一种都可以立即被识别为表示成功或失败。因此，引理1.8.10和1.8.11确实证明了该算法是一个约束求解器。

### 1.9 从ML微积分到ML编程语言

在本节中，我们说明了如何扩展到目前为止开发的框架以容纳基本类型（如整数）的值、对、和、引用以及递归函数定义的操作。然后，我们描述了更复杂的扩展，即代数数据类型定义、模式匹配和类型注解。最后，简要讨论了与递归类型相关的问题。异常处理没有讨论；读者可以参考（TAPL第14章）。

## 简单扩展

通过引入新的常量并适当地扩展 $\xrightarrow{\delta}$ 和 $\Gamma_{0}$，可以将编程语言ML的许多特性引入到ML演算中。在每种情况下，都有必要检查是否满足定义1.7.6的要求，即新的初始环境是否真实反映了新常量的本质以及新简化规则的行为。下面，我们单独描述了几个这样的扩展。

1.9.1 练习 [整数，推荐，$\star \star$ ]：整数字面量和整数加法在例子1.2.1、1.2.2和1.2.4中已经介绍并赋予了操作语义。现在让我们引入一个独立的类型构造器int，其签名是$\star$，并用对每个整数$n$的绑定$\hat{n}$ : int以及$\hat{+}:$ int $\rightarrow$ int $\rightarrow$ int来扩展初始环境$\Gamma_{0}$。检查这些定义是否符合定义1.7.6的要求。

1.9.2 练习 [布尔值，推荐，$\star \star, \nrightarrow$ ]：布尔值和条件语句在练习1.2.6中已经介绍并给出了操作语义。引入一个独立的类型构造器bool来表示布尔值，并解释如何扩展初始环境。检查你的定义是否符合定义1.7.6的要求。对于语法糖 if $t_{0}$ then $t_{1}$ else $t_{2}$ 的约束生成规则是什么？

1.9.3 练习 [对偶, $\star \star, \nrightarrow$]：对偶及其对偶投影已在例子1.2.3和1.2.5中引入并赋予了操作语义。现在让我们引入一个孤立的类型构造器 $\times$，其签名是 $\star \otimes \star \Rightarrow \star$，在其两个参数上都是协变的，并扩展初始环境 $\Gamma_{0}$ 以包含以下绑定：

$$
\begin{aligned}
(\cdot, \cdot): & \forall \mathrm{XY} . \mathrm{X} \rightarrow \mathrm{Y} \rightarrow \mathrm{X} \times \mathrm{Y} \\
\pi_{1}: & \forall \mathrm{XY} . \mathrm{X} \times \mathrm{Y} \rightarrow \mathrm{X} \\
\pi_{2}: & \forall \mathrm{XY} . \mathrm{X} \times \mathrm{Y} \rightarrow \mathrm{Y}
\end{aligned}
$$

检查这些定义是否符合1.7.6定义的要求。

1.9.4 练习 [和, $\star \star, \nrightarrow$ ]：和已在例1.2.7中引入并赋予了操作语义。现在让我们引入一个孤立的类型构造器+，其签名是 $\star \otimes \star \Rightarrow \star$，在其两个参数中都是协变的，并用以下绑定扩展初始环境 $\Gamma_{0}$：

$$
\begin{aligned}
\operatorname{inj}_{1}: & \forall X Y . X \rightarrow \mathrm{X}+\mathrm{Y} \\
\mathrm{inj}_{2}: & \forall \mathrm{XY.Y} \rightarrow \mathrm{X}+\mathrm{Y} \\
\text { case }: & \forall \mathrm{XYZ} .(\mathrm{X}+\mathrm{Y}) \rightarrow(\mathrm{X} \rightarrow \mathrm{Z}) \rightarrow(\mathrm{Y} \rightarrow \mathrm{Z}) \rightarrow \mathrm{Z}
\end{aligned}
$$

检查这些定义是否符合1.7.6定义的要求。

1.9.5 练习 [参考文献，***]：参考文献已在例1.2.9中介绍并赋予了操作语义。类型构造器ref已在定义1.7.4中引入。现在让我们用以下绑定扩展初始环境$\Gamma_{0}$：

$$
\begin{aligned}
\text { ref }: & \forall X . X \rightarrow \operatorname{ref} X \\
!: & \forall X . \operatorname{ref} X \rightarrow X \\
:=: & \forall X . \operatorname{ref} X \rightarrow X \rightarrow X
\end{aligned}
$$

检查这些定义是否符合1.7.6定义的要求。

1.9.6 练习[递归，推荐，$\star \star \star$]：在示例1.2.10中引入了固定点组合子fix，并给出了其操作语义。现在让我们用以下绑定扩展初始环境$\Gamma_{0}$：

$$
\text { fix : } \quad \forall X Y .((X \rightarrow Y) \rightarrow(X \rightarrow Y)) \rightarrow X \rightarrow Y
$$

检查这些定义是否符合1.7.6定义的要求。回想一下在例1.2.10中是如何定义letrec语法糖的，并检查这是否产生了以下约束生成规则：

$$
\begin{aligned}
& \text { let } \Gamma_{0} \text { in } \llbracket \text { letrec } f=\lambda z . \mathrm{t}_{1} \text { in } \mathrm{t}_{2}: \mathrm{T} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in let } \mathrm{f}: \forall \mathrm{XY}\left[\text { let } \mathrm{f}: \mathrm{X} \rightarrow \mathrm{Y} ; \mathrm{z}: \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{Y} \rrbracket\right] \mathrm{X} \rightarrow \mathrm{Y} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket
\end{aligned}
$$

注意这个约束的某种奇特结构：程序变量$f$在其中绑定两次，具有不同的类型方案。该约束要求在$t_{1}$中出现的所有$f$被分配为单态类型$\mathrm{X} \rightarrow \mathrm{Y}$。然而，在检查$t_{2}$之前，这种类型被泛化并转换成一种类型方案，因此$t_{2}$中$f$的每次出现可能像通常的let多态性一样接收不同的类型。在1.10节（第113页）讨论了一种更强大的类型检查递归函数定义的方法。

代数数据类型

练习1.9.3和1.9.4展示了如何用二元、匿名积和和来扩展语言。这些构造虽然很通用，但仍有几个缺点。首先，它们仅限于二元，而我们希望有$k$元积和和，任意$k \geq 0$。这样的推广当然是直接的。其次，更有趣的是，它们的组件必须通过数字索引（如“请提取对的第二个组件”）来引用，而不是通过名称（“提取名为y的组件”）。在实践中，使用名称至关重要，因为它们使程序更易读，在面对变化时更有弹性。人们可以引入一种机制，允许将名称定义为数字索引的语法糖。这将有所帮助，但帮助不大，因为名称仍然不会出现在类型中，类型仍然由匿名积和和组成。第三，在没有递归类型的情况下，积和和的表达能力不足以允许定义无界数据结构，如列表。实际上，很容易看出，任何类型为$\mathrm{T}$的值，由基本类型（int，bool等），积和和组成，其大小必须是有限的，其中界限$|\mathrm{T}|$是T的函数。更准确地说，考虑到常数因子，我们有 $\mid$ int $|=|$ bool $\mid=1$， $\left|\mathrm{T}_{1} \times \mathrm{T}_{2}\right|=1+\left|\mathrm{T}_{1}\right|+\left|\mathrm{T}_{2}\right|$，以及$\left|\mathrm{T}_{1}+\mathrm{T}_{2}\right|=1+\max \left(\left|\mathrm{T}_{1}\right|,\left|\mathrm{T}_{2}\right|\right)$。下面的例子描述了同一问题的另一个方面。

1.9.7 示例：一个列表要么为空，要么是一个元素与另一个列表的配对。因此，尝试将列表类型编码为某种任意类型（例如，单位）的和，一方面，以及元素类型与列表类型本身的乘积的和，似乎是很自然的。考虑到这种编码，我们可以继续编写代码 - 例如，一个计算列表长度的函数：

$$
\text { letrec length }=\lambda \text { l.case } 1\left(\lambda_{-} . \hat{0}\right)\left(\lambda z . \hat{1} \hat{+} \text { length }\left(\pi_{2} z\right)\right)
$$

我们使用了整数、对偶、和以及前一部分介绍的letrec构造。代码通过一个案例结构分析列表1。如果选择了左分支，列表为空，因此返回0。如果选择了右分支，那么$z$被绑定到一个元素和列表尾部的对偶上。后者是通过使用投射算子$\pi_{2}$获得的。其长度是通过递归调用length计算的并增加1。这段代码非常有意义。然而，应用约束生成和约束求解算法最终会导致形如$\mathrm{X}=\mathrm{Y}+(\mathrm{Z} \times \mathrm{X})$的方程，其中$\mathrm{X}$代表1的类型。这个方程准确反映了我们对列表类型的编码。然而，在句法模型中，它没有解，所以我们对长度的定义是类型错误的。可以采用自由正则树模型，从而将等递归类型引入系统（TAPL第20章）；然而，有充分的理由不这样做（第106页）。

为了解决这个问题，编程语言ML提供了代数数据类型定义，其优雅之处在于，它们在只进行了适度的理论扩展的同时，确实解决了上述三个问题。代数数据类型可以看作是一种抽象类型，被声明为与具有命名组件的（$k$元）积类型或和类型同构。每个组件的类型也被声明，并且可以引用正在定义的代数数据类型：因此，代数数据类型是同递归的（TAPL第20章）。为了在声明每个组件的类型时提供足够的灵活性，代数数据类型定义可以通过多个类型变量进行参数化。最后，为了允许描述复杂的数据结构，有必要同时定义多个代数数据类型；定义然后可以是相互递归的。实际上，为了简化这种形式化的呈现，我们假设所有代数数据类型在程序开始时一次性定义。这个决定当然与模块化编程相冲突，但除此之外并不会成为问题。

在以下内容中，D 范围涵盖了一组数据类型。我们假设数据类型构成了类型构造子的一个子集。我们要求它们每一个都是孤立的，并且具有形式为 $\vec{\kappa} \Rightarrow \star$ 的签名。此外，$\ell$ 范围涵盖了一个标签集合 $\mathcal{L}$，我们既可以将其作为数据构造器，也可以作为记录标签来使用。代数数据类型的定义要么是变体类型定义，要么是记录类型定义，它们各自的形式为：

$$
\mathrm{D} \overrightarrow{\mathrm{X}} \approx \sum_{i=1}^{k} \ell_{i}: \mathrm{T}_{i} \quad \text { and } \quad \mathrm{D} \overrightarrow{\mathrm{X}} \approx \prod_{i=1}^{k} \ell_{i}: \mathrm{T}_{i}
$$

在任一情况下，$k$ 必须是非负的。如果 $\mathrm{D}$ 有签名 $\vec{\kappa} \Rightarrow \star$，那么类型变量 $\overrightarrow{\mathrm{X}}$ 必须有种类 $\vec{\kappa}$。每个 $\mathrm{T}_{i}$ 必须有种类 $\star$。我们将 $\overline{\mathrm{X}}$ 称为参数，将 $\overrightarrow{\mathrm{T}}$（由 $\mathrm{T}_{1}, \ldots, \mathrm{T}_{k}$ 形成的向量）称为定义的组件。参数在组件内绑定，定义必须是闭合的，即必须满足 $f t v(\overrightarrow{\mathrm{T}}) \subseteq \overline{\mathrm{x}}$。最后，为了使代数数据类型定义有效，类型构造器 $\mathrm{D}$ 关于子类型的 行为必须与其定义相匹配。这一要求在下面会进一步阐明。

1.9.8 定义：考虑一个代数数据类型的定义，其参数和组件分别是 $\vec{X}$ 和 $\vec{T}$。设 $\vec{X}^{\prime}$ 和 $\vec{T}^{\prime}$ 是它们在任意重命名下的像。那么，必须满足 $\mathrm{D} \overrightarrow{\mathrm{X}} \leq \mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \Vdash \overrightarrow{\mathrm{T}} \leq \overrightarrow{\mathrm{T}}^{\prime}$。

上述要求与模型中子类型的定义有关。这个概念是，既然声明 $\mathrm{D} \overrightarrow{\mathrm{X}}$ 与（$\overrightarrow{\mathrm{T}}$ 的和或积）同构，那么只要用 $\mathrm{D}$ 构建的两个类型可以比较，它们的展开也应该可以比较。类型的健全性不需要逆向蕴含断言，而且有时声明不验证它的代数数据类型是很有用的——即所谓的幻影类型（Fluet 和 Pucella, 2002）。请注意，通过使类型构造器 $\mathrm{D}$ 在其所有参数上不变，这个要求总是可以得到满足的。实际上，在这种情况下，$D \vec{X} \leq D \vec{X}^{\prime}$ 蕴含着 $\vec{X}=\vec{X}^{\prime}$，这又必须蕴含 $\overrightarrow{\mathrm{T}}=\overrightarrow{\mathrm{T}}^{\prime}$，因为 $\overrightarrow{\mathrm{T}}^{\prime}$ 恰好是 $\left[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{X}^{\prime}}\right] \overrightarrow{\mathrm{T}}$。在无等式树模型中，每个类型构造器自然是不变的，因此这个要求是微不足道的。然而，在其他设置中，通常可以在给 $\mathrm{D}$ 分配较少限制的变异性时满足定义 1.9 .8 的要求。下面的例子说明了这样的情况。

1.9.9 示例：设列表是一种签名 $\star \Rightarrow \star$ 的数据类型。设 Nil 和 Cons 为数据构造器。那么，以下是列表作为一种变体类型的定义：

$$
\text { list } \mathrm{X} \approx \Sigma(\mathrm{Nil}: \text { unit; Cons }: \mathrm{X} \times \text { list } \mathrm{X})
$$

因为数据类型是类型构造器的子集，即使在定义列表的含义的过程中，也可以在等式右侧形成类型列表X。换句话说，数据类型定义可以是递归的。然而，由于≈不被解释为等式，类型列表X并不是一个递归类型：它不过是将一元类型构造器列表应用于类型变量X。为了检查列表定义是否符合1.9.8定义的要求，我们必须确保

$$
\text { list } \mathrm{X} \leq \text { list } \mathrm{X}^{\prime} \Vdash \text { unit } \leq \text { unit } \wedge \mathrm{X} \times \text { list } \mathrm{X} \leq \mathrm{X}^{\prime} \times \text { list } \mathrm{X}^{\prime}
$$

保持。这个断言等价于列表 $\mathrm{X} \leq$ 列表 $\mathrm{X}^{\prime} \Vdash \mathrm{X} \leq \mathrm{X}^{\prime}$。为了满足要求，只需将列表定义为协变类型构造器即可，即在设计模型中的子类型时使得列表 $\mathrm{X} \leq$ 列表 $\mathrm{X}^{\prime} \equiv \mathrm{X} \leq \mathrm{X}^{\prime}$ 成立。

让树成为签名 $\star \Rightarrow \star$ 的数据类型。让根和子成为记录标签。那么，以下是对树作为记录类型的定义：

$$
\text { tree } \mathrm{X} \approx \Pi(\text { root }: \mathrm{X} ; \text { sons }: \text { list }(\text { tree } \mathrm{X}))
$$

这个定义又是递归的，并且依赖于之前的定义。因为列表是协变的，很容易验证，如果树也被制成一个协变类型构造器，那么树的定义是有效的。

1.9.10 练习 $[\star \star, \nrightarrow]$ ：考虑一个非递归代数数据类型定义，其中出现在右侧的每个类型构造器的变化性是已知的。你能否系统地确定，对于每个参数，使得定义有效的最小限制性变化性？将此过程推广到递归和相互递归代数数据类型定义的情况。

序言是一组代数数据类型定义，其中每种数据类型最多定义一次，每个数据构造器或记录标签最多出现一次。一个程序是由一个序言和一个表达式组成的对。序言的效果是丰富了编程语言的新常量。也就是说，变体类型定义通过几个注入和一个案例构造扩展了操作语义，如示例1.2.7所示。记录类型定义通过一个记录形成构造和几个投影扩展它，如示例1.2.3和1.2.5所示。在任一情况下，初始类型环境 $\Gamma_{0}$ 都会扩展有关这些新常量的信息。因此，代数数据类型定义可以被视为一种简单的配置语言，它允许指定在ML-计算器的哪个实例中应检查和解释序言后面的表达式。现在，让我们准确地描述这一现象。

首先，假设序言包含定义 $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \sum_{i=1}^{k} \ell_{i}: \mathrm{T}_{i}$。那么，对于每个 $i \in\{1, \ldots, k\}$，引入一个一元构造器，名为 $\ell_{i}$。此外，还引入了一个 $k+1$ 元的析构器，名为 case D $_{D}$。当 $k>0$ 时，通常将 case $\mathrm{t}\left[\ell_{i}: \mathrm{t}_{i}\right]_{i=1}^{k}$ 写作应用 case $_{D} t t_{1} \ldots t_{n}$。操作语义通过以下归约规则进行扩展，对于 $i \in\{1, \ldots, k\}$ ：

$$
\begin{equation*}
\operatorname{case}\left(\ell_{i} \mathrm{v}\right)\left[\ell_{j}: \mathrm{v}_{j}\right]_{j=1}^{k} \xrightarrow{\delta} \mathrm{v}_{i} \mathrm{v} \tag{R-ALG-CASE}
\end{equation*}
$$

对于每个$i \in \{1, \ldots, k\}$，初始环境通过绑定$\ell_{i}: \forall \overline{\mathrm{X}} . \mathrm{T}_{i} \rightarrow \mathrm{D} \overrightarrow{\mathrm{X}}$进行扩展。它进一步通过绑定情况$\mathrm{D}_{\mathrm{D}}: \forall \overline{\mathrm{X}} \mathrm{Z} . \mathrm{D} \overrightarrow{\mathrm{X}} \rightarrow (\mathrm{T}_{1} \rightarrow \mathrm{Z}) \rightarrow \ldots (\mathrm{T}_{k} \rightarrow \mathrm{Z}) \rightarrow \mathrm{Z}$进行扩展。

现在，假设序言包含了定义 $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \prod_{i=1}^{k} \ell_{i}: \mathrm{T}_{i}$。那么，对于每个 $i \in\{1, \ldots, k\}$，引入了一个元数为1的析构函数，名为 $\ell_{i}$。此外，引入了一个元数为$k$的构造函数，名为 make $\mathrm{e}_{\mathrm{D}}$。通常将 $\mathrm{t} . \ell$ 写作应用 $\ell \mathrm{t}$，并且当 $k>0$ 时，将 $\left\{\ell_{i}=\mathrm{t}_{i}\right\}_{i=1}^{k}$ 写作应用 make $\mathrm{t}_{\mathrm{D}} \ldots \mathrm{t}_{k}$。操作语义通过以下缩减规则扩展，对于 $i \in\{1, \ldots, k\}$ ：

$$
\begin{equation*}
\left(\left\{\ell_{j}=\mathrm{v}_{j}\right\}_{j=1}^{k}\right) \cdot \ell_{i} \xrightarrow{\delta} \mathrm{v}_{i} \tag{R-ALG-PRoJ}
\end{equation*}
$$

对于每个$i \in \{1, \ldots, k\}$，初始环境通过绑定$\ell_{i}: \forall \overline{\mathrm{X}} . \mathrm{D} \overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}_{i}$进行扩展。它进一步通过绑定make $\mathrm{D}_{\mathrm{D}}: \forall \overline{\mathrm{X}} . \mathrm{T}_{1} \rightarrow \ldots \rightarrow \mathrm{T}_{k} \rightarrow \mathrm{D} \overrightarrow{\mathrm{X}}$进行扩展。

1.9.11 示例：定义列表（示例1.9.9）的效果是使Nil和Cons数据构造函数的元数为1，并引入一个二进制析构器case list。该定义还以下列方式扩展了初始环境：

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-090.jpg?height=140&width=887&top_left_y=1880&top_left_x=712)

因此，值 Cons $(\hat{0}, \mathrm{Nil}())$，一个长度为1的整数列表，具有类型list int。现在可以如下编写计算列表长度的函数：

$$
\text { letrec length }=\lambda l . \text { case } 1\left[\mathrm{Nil}: \lambda \_. \hat{0} \mid \text { Cons }: \lambda z . \hat{1} \hat{+} \text { length }\left(\pi_{2} z\right)\right]
$$

回忆一下，这个表示法是语法糖，用于表示


$$
\text { letrec length }=\lambda \text { l.case }_{\text {list }} l\left(\lambda \_. \hat{0}\right)\left(\lambda z . \hat{1} \hat{+} \text { length }\left(\pi_{2} z\right)\right)
$$

与1.9.7例中的代码差异看起来很小：现在的case构造被注释上了数据类型list。因此，类型推断算法使用了分配给case list的类型方案，这是从list的定义派生而来的，而不是分配给1.9.4练习中给出的匿名case构造的类型方案。这样做有几个好处。首先，前者比后者更具信息性，因为它包含了与数据构造器$\ell_{i}$相关的类型$\mathrm{T}_{i}$。例如，这里生成的约束要求$\mathrm{z}$的类型为$\mathrm{X} \times$ list $\mathrm{X}$，对于某个$\mathrm{X}$，如果在第二个分支中犯了一个错误，比如省略了$\pi_{2}$的使用，就会给出一个好的错误信息。其次，更重要的是，即使在没有递归类型的情况下，代码现在也是类型正确的。在1.9.7例中，产生了循环方程，因为case要求1的类型为和类型，并且和类型将其左右分支的类型作为子项携带。而在这里，case list要求1具有某种X的list类型。这是一个抽象类型：它不显式地包含分支的类型。因此，生成的约束不再涉及循环方程。实际上，它是可满足的；读者可以验证length确实具有预期的类型$\forall x$. list $X \rightarrow$ int。

示例1.9.11强调了使用声明的抽象类型，而不是匿名的具体和或积类型，以避免需要递归类型。这一技巧的本质在于，与代数数据类型上的操作相关联的类型方案会隐式地折叠和展开数据类型的定义。更准确地说，让我们回忆一下在（k元）匿名和的情况下分配给第$i^{\text {th }}$注入的类型方案：它是$\forall \mathrm{X}_{1} \ldots \mathrm{X}_{k} \cdot \mathrm{X}_{i} \rightarrow \mathrm{X}_{1}+\ldots+\mathrm{X}_{k}$，或者更简洁地说，$\forall \mathrm{x}_{1} \ldots \mathrm{X}_{k} . \mathrm{X}_{i} \rightarrow \sum_{i=1}^{k} \mathrm{X}_{i}$。通过将每个$\mathrm{X}_{i}$实例化为$\mathrm{T}_{i}$并再次泛化，我们发现了一个更具体的类型方案$\forall \overline{\mathrm{X}} . \mathrm{T}_{i} \rightarrow \sum_{i=1}^{k} \mathrm{~T}_{i}$。这或许可以成为分配给$\ell_{i}$的类型方案？然而，实际上它是$\forall \overline{\mathrm{X}}$。$\mathrm{T}_{i} \rightarrow \mathrm{D} \overrightarrow{\mathrm{X}}$。我们现在意识到这个类型方案不仅反映了第$i^{\text {th }}$注入的操作行为，还通过将定义右侧的匿名和$\sum_{i=1}^{k} \mathrm{~T}_{i}$转换为定义左侧的参数化抽象类型$D \vec{X}$，折叠了代数数据类型$\mathrm{D}$的定义。相反，分配给case $_{D}$的类型方案展开了定义。在记录类型的情况下情况相同：在任一情况下，构造函数折叠，析构函数展开。换句话说，代码中出现的数据构造器和记录标签可以被视为类型检查器显式地折叠或展开代数数据类型定义的指令。这种机制是等递归类型的特征。

1.9.12 练习 $[\star, \nrightarrow]$ ：对于固定的 $k$，检查与 $k$ 元匿名乘积相关的所有机制 - 即构造函数、析构函数、归约规则以及对初始类型环境的扩展 - 可以被视为由单个代数数据类型定义的结果。在 $k$ 元匿名和的情况下进行类似的检查。

1.9.13 练习 $[\star \star \star, \nrightarrow]$ ：检查上述定义是否符合定义1.7.6的要求。

1.9.14练习 $[\star \star \star, \nrightarrow]$ ：为了简单起见，我们假设数据构造器总是为一元的。实际上，可以允许任何元数的数据构造器，并将变体定义为 $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \sum_{i=1}^{k} \ell_{i}: \overrightarrow{\mathrm{T}}_{i}$。例如，列表的定义可以是 list $\mathrm{X} \approx \Sigma(\mathrm{Nil}$；Cons $: \mathrm{X} \times$ list $\mathrm{X})$，例如 $\operatorname{Cons}(\hat{0}, \mathrm{Nil})$ 就是一个列表值。在上面的定义中进行必要的更改，并检查它们是否仍符合定义1.7.6的要求。

在这份代数数据类型的正式介绍中，我们假设在程序类型检查之前已知所有代数数据类型的定义。这种简化假设是由以下事实强加给我们的：我们是在一个固定的模型中解释约束，也就是说，我们假设有一个固定的类型宇宙。在实践中，编程语言有模块系统，允许不同的模块拥有对类型宇宙的不同、部分视图。这样，每个模块都可以有自己的数据类型定义。有趣的是，原则上甚至可以将单个数据类型的定义分散在几个模块中，从而产生可扩展的代数数据类型。例如，模块A可能声明存在一个参数化变体类型D$x$，但不给出其组件。稍后，模块B可能定义一个组件$\ell: \mathrm{T}$，其中$f t v(\mathrm{~T}) \subseteq \overline{\mathrm{X}}$。这样的定义使得$\ell$成为一个一元构造器，其类型方案与之前一样是$\forall \overline{\mathrm{X}} . \mathrm{T} \rightarrow \mathrm{D} \overrightarrow{\mathrm{X}}$。然而，不可能引入一个析构器$\mathrm{case}_{\mathrm{D}}$，因为可扩展变体类型的定义永远不能被认为是完整的——其他未知的模块可能会进一步扩展它。为了补偿它的缺失，可以给每个构造器$\ell$补充一个析构器$\ell^{-1}$，其语义由$\ell^{-1}(\ell \mathrm{v}) \mathrm{v}_{1} \mathrm{v}_{2} \xrightarrow{\delta} \mathrm{v}_{1} \mathrm{v}$和$\ell^{-1}\left(\ell^{\prime} \mathrm{v}\right) \mathrm{v}_{1} \mathrm{v}_{2} \xrightarrow{\delta} \mathrm{v}_{2}\left(\ell^{\prime} \mathrm{v}\right)$给出，当$\ell \neq \ell^{\prime}$，其类型方案是$\forall \overline{\mathrm{x}} \mathrm{Z} . \mathrm{D} \overrightarrow{\mathrm{X}} \rightarrow(\mathrm{T} \rightarrow \mathrm{Z}) \rightarrow(\mathrm{D} \overrightarrow{\mathrm{X}} \rightarrow \mathrm{Z}) \rightarrow \mathrm{Z}$。当模式匹配可用时，$\ell^{-1}$实际上可以在语言中定义。ML编程语言并没有提供作为语言特性的可扩展代数数据类型，但它有一个内置的可扩展变体类型，即异常类型exn。因此，可以在任何模块内为类型exn定义新的构造器。这种额外灵活性的代价是无法对类型为exn的值进行穷举的情况分析。

代数数据类型定义的一个重大缺点在于，标签ℓ不能被两个不同的变体或记录类型定义共享。实际上，每个代数数据类型定义都通过新的常量扩展了计算。严格地说，我们的表述不允许将单个常量c与两个不同的定义相关联。即使我们允许这种碰撞，初始环境也会包含c的两个绑定，其中之一将变得无法访问。这种现象在实际的ML编程语言实现中出现，其中一个新的代数数据类型定义可能会隐藏之前定义的一些数据构造器或记录标签。第1.11节讨论了这种表达性不足的优雅解决方案。

## Pattern matching

我们的产品、总和以及代数数据类型的呈现一直保持在ML-演算的设定内：也就是说，数据结构是由构造器构建的，而案例分析和记录访问操作被视为析构器。为恢复标准表示法，我们使用了一些语法糖。该语言现在足够表达性，允许定义和操作复杂的数据结构，如列表和树。然而，经验表明，在这种语言中进行编程仍然有些麻烦。实际上，案例分析和记录访问是低级操作：前者允许检查标签和分支，而后者允许取消引用指针。在实践中，通常需要执行更复杂的任务，例如确定数据结构是否具有某种形状或两个数据结构是否具有可比较的形状。目前，执行这些任务的唯一方法是编程一个显式的低级操作序列。如果能够扩展语言，使其直接允许描述称为模式的形状，并使检查模式是否与值匹配成为基本操作，那将更为可取。ML-编程语言提供了这个特性，称为模式匹配。尽管可以通过引入一组析构器将模式匹配添加到ML-演算中，但我们更愿意通过一个新的匹配构造来扩展演算，这个匹配构造包含了现有的let构造。这种方法似乎更简单、更强大。我们现在进行这个操作。

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-094.jpg?height=383&width=1520&top_left_y=224&top_left_x=240)

图1-13：模式和模式匹配

extension.

让我们首先定义模式（图1-13）的语法，并非正式地描述（目前是这样）它们匹配哪些值。对于一个模式p，我们关联一组已定义的程序变量dpi(p)，其定义在下面的文本中出现。模式p是良构的当且仅当dpi(p)是有定义的。首先，通配符_是一个模式，它匹配任何值并且不绑定任何变量。我们让dpi(_) = ∅。尽管通配符可以被看作是一个匿名变量，我们到目前为止都是这样做的，但现在更简单的方法是将其视为一个独特的模式。程序变量z也是一个模式，它匹配任何值并将z绑定到匹配的值。我们让dpi(z) = {z}。接下来，如果c是一个k元构造器，那么c p1 ... pk是一个模式，当且仅当对于每个i∈{1,...,k}，pi匹配vi时，它匹配c v1 ... vk。我们让dpi(c1 ... pk) = dpi(p1) ∪ ... ∪ dpi(pk)。也就是说，当p1,...,pk定义了互不相交的变量集时，模式c p1 ... pk是良构的。这个条件排除了如(z, z)之类的非线性模式。定义这种模式的语义需要在每个类型上都有相等性的概念，这会引入各种复杂性，因此通常被认为是非良构的。模式p1 ∧ p2匹配所有p1和p2都匹配的值。它通常与p2是一个程序变量一起使用：这样，它允许同时检查一个值的形状并将名称绑定到它。再次，我们定义dpi(p1 ∧ p2) = dpi(p1) ∪ dpi(p2)。模式p1 ∨ p2匹配所有p1或p2匹配的值。我们定义dpi(p1 ∨ p2) = dpi(p1) = dpi(p2)。也就是说，当p1和p2定义相同的变量时，模式p1 ∨ p2是良构的。因此，(inj1 z) ∨ (inj2 z)是一个良构的模式，它将z绑定到二元和的组件，而不管它的标签是什么。然而，(inj1 z1) ∨ (inj2 z2)是非良构的，因为静态上无法预测它定义的是z1还是z2。

让我们现在正式定义一个模式 p 是否与一个值 v 匹配，以及 dp(i(p)) 中的变量在过程中如何绑定到值。这是通过引入一种广义的替换，记作 [p → v]，它可以是以下两种情形之一：

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-095.jpg?height=296&width=1510&top_left_y=227&top_left_x=232)

未定义，或者是在程序变量 $d p i(p)$ 中的值替换。如果是前者，那么 $p$ 不匹配 $v$。如果是后者，那么 $p$ 匹配 $v$，并且对于每个 $z \in d p i(p)$，变量 $z$ 绑定到值 $[p \mapsto v]z$。当然，当 $p$ 是变量 $z$ 时，广义替换 $[z \mapsto v]$ 是定义良好的，并且与替换 $[z \mapsto v]$ 相同，这证明了我们滥用记号的合理性。为了构建广义替换，我们使用了两个简单的组合子。首先，当 $dpi(p_1)$ 和 $dpi(p_2)$ 不相交时，$[p_1 \mapsto v_1] \otimes [p_2 \mapsto v_2]$ 表示 $[p_1 \mapsto v_1]$ 和 $[p_2 \mapsto v_2]$ 的集合论并集，如果两者都定义良好，否则未定义。我们使用这个组合子确保 $p_1$ 匹配 $v_1$ 和 $p_2$ 匹配 $v_2$，并将两个相应的绑定集合并。其次，当 $o_1$ 和 $o_2$ 是两个可能未定义的数学对象，在定义时属于同一空间，$o_1 \oplus o_2$ 表示 $o_1$（如果它已定义），否则表示 $o_2$——即 $\oplus$ 是一个左倾的天使选择操作符。特别是，当 $dpi(p_1)$ 和 $dpi(p_2)$ 重合时，$[p_1 \mapsto v_1] \oplus [p_2 \mapsto v_2]$ 表示 $[p_1 \mapsto v_1]$（如果它已定义），否则表示 $[p_2 \mapsto v_2]$。我们使用这个组合子确保 $p_1$ 匹配 $v_1$ 或者 $p_2$ 匹配 $v_2$，并保留相应的绑定集。广义替换的完整定义，依赖于这些组合子，出现在图1-13中。它反映了前一段的非正式介绍。

一旦定义了模式和模式匹配，扩展ML-演算的语法和操作语义就非常直接。我们将表达式语法丰富为一个新构造，匹配 $\mathrm{t}$ 与 $\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$，其中 $k \geq 1$。它由一个项 $t$ 和一个非空、有序的子句列表组成，每个子句由一个模式 $\mathrm{p}_{i}$ 和一个项 $\mathrm{t}_{i}$ 组成。评估上下文的语法也得到了扩展，使得正在检查的项 $t$ 首先被简化为一个值 $\mathrm{v}$。操作语义通过一个新规则 $\mathrm{R}-\mathrm{MATCH}$ 进行扩展，该规则指出，匹配 $\mathrm{v}$ 与 $\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$ 可简化为 $\left[\mathrm{p}_{i} \mapsto \mathrm{v}\right] \mathrm{t}_{i}$，其中 $i$ 是 $\{1, \ldots, k\}$ 中最小的元素，使得 $\mathrm{p}_{i}$ 匹配 $\mathrm{v}_{i}$。技术上，$\bigoplus_{i=1}^{k}\left[\mathrm{p}_{i} \mapsto \mathrm{v}\right] \mathrm{t}_{i}$ 表示 $\left[\mathrm{p}_{1} \mapsto \mathrm{v}\right] \mathrm{t}_{1} \oplus \ldots \oplus\left[\mathrm{p}_{k} \mapsto \mathrm{v}\right] \mathrm{t}_{k}$，这样简化后的结果是这个序列中第一个定义的项。

就语义学而言，匹配构造可以被视为let构造的泛化。实际上，let $z=t_{1}$ in $t_{2}$ 现在可以被视为是 match $t_{1}$ with $z . t_{2}$ 的语法糖，即一个具有单一子句和变量模式的匹配构造。那么，R-LET就成了R-MATCH的一个特例。

引入一些更多的语法糖是令人愉悦的。我们用 $\lambda\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$ 表示 $\lambda$ z.match $\mathrm{z}$ with $\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$，其中 $\mathrm{z}$ 对于 $\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$ 是新鲜的。因此，可以通过案例来定义函数，这是ML编程语言中的一种常见习惯用法。

1.9.15 示例：使用模式匹配，现在可以如下编写计算列表长度（示例1.9.11）的函数：

$$
\text { letrec length }=\lambda\left(\mathrm{Nil}_{\ldots} . \hat{0} \mid \operatorname{Cons}\left(\_, z\right) . \hat{1} \hat{+} \text { length } z\right)
$$

第二种模式匹配非空列表，并同时将 $\mathrm{z}$ 绑定到其尾部，这样就无需显式应用 $\pi_{2}$。

1.9.16 练习 $[**$, 推荐, $\nrightarrow$ ]：在上述长度的定义下，考虑长度应用于列表 Cons( $\hat{0}$, $\mathrm{Nil}()$) 的应用。消除语法糖后，确定这个表达式通过哪个归约序列被简化为一个值。

在我们能够继续并将类型系统扩展以处理新的匹配构造之前，我们必须对约束的语法和含义做两个轻微的扩展。首先，如果 $\sigma$ 是 $\forall \overline{\mathrm{X}}[C].T$，其中 $\overline{\mathrm{X}} \# f t v\left(\mathrm{T}^{\prime}\right)$，那么 $\mathrm{T}^{\prime} \preceq \sigma$ 代表约束 $\exists \overline{\mathrm{X}} .(C \wedge \mathrm{T}^{\prime} \leq \mathrm{T})$。这种关系与实例关系（定义1.3.3）相同，只是子类型的方向相反。我们通过引入形式为 $\mathrm{T} \preceq \mathrm{x}$ 的实例化约束来扩展约束的语法，并通过添加CM-的对称对应物来定义它们的含义。

实例。我们注意到，当子类型被解释为等价时，关系 $\sigma \preceq \mathrm{T}$ 和 $\mathrm{T} \preceq \sigma$ 是一致的，因此在那个特定情况下这种扩展是不必要的。其次，我们扩展了环境语法，以便连续的多个绑定可以共享一组量词和约束。也就是说，我们允许写成 $\forall \overline{\mathrm{X}}[C] .\left(\mathrm{x}_{1}: \mathrm{T}_{1} ; \ldots ; \mathrm{x}_{k}: \mathrm{T}_{k}\right)$，对于 $\mathrm{x}_{1}: \forall \overline{\mathrm{x}}[C] . \mathrm{T}_{1} ; \ldots ; \mathrm{x}_{k}$ : $\forall \overline{\mathrm{X}}[C] . \mathrm{T}_{k}$。从理论角度来看，这不过是语法糖；然而，在实践中，字面上实现这种新习惯用语是有用的，因为它避免了不必要的复制约束 $C$。

让我们现在扩展类型系统。为了简洁起见，我们仅扩展约束生成规则。当然，也有可能定义先前展示的基于规则的类型系统相应的扩展，即 $\mathrm{DM}, \operatorname{HM}(X)$ 和 $\operatorname{PCB}(X)$。我们首先定义一个约束 $\llbracket \mathrm{T}: \mathrm{p} \rrbracket$，它表示类型 $\mathrm{T}$ 的值作为模式 $\mathrm{p}$ 可接受输入的必要且充分条件。其自由类型变量是以下子集。

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

图1-15：模式和模式匹配的约束生成

$f t v(T)$，而其自由程序标识符要么是构造器，要么是由 $\mathrm{p}$ 绑定的程序变量。它定义在图1-15的上部。第一条规则表明通配符匹配任意类型的值。第二条和第三条规则管理模式中的程序变量和构造器应用。它们与表达式中管理这些构造的规则相同（第59页），除了子类型的方向相反。在没有子类型的情况下，它们将是完全相同的。我们用 $\overrightarrow{\mathrm{X}}$ 表示 $\mathrm{X}_{1} \ldots \mathrm{X}_{k}$，用 $\overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}$ 表示 $\mathrm{X}_{1} \rightarrow \ldots \rightarrow \mathrm{X}_{k} \rightarrow \mathrm{T}$。像往常一样，类型变量 $\mathrm{X}_{1}, \ldots, \mathrm{X}_{k}$ 必须具有 $\star$ 类型的种类，并且对于等式的左侧必须是不同且新鲜的。最后两条规则简单地将类型 $\mathrm{T}$ 分发到两个子模式中。很容易检查 $\llbracket \mathrm{T}: \mathrm{p} \rrbracket$ 在 $\mathrm{T}$ 上是反变的：

1.9.17 引理：$\mathrm{T}^{\prime} \leq \mathrm{T} \wedge \llbracket \mathrm{T}: \mathrm{p} \rrbracket$ 推出 $\llbracket \mathrm{T}^{\prime}: \mathrm{p} \rrbracket$.

这个属性反映了事实$\mathrm{T}$代表了模式p的一个输入类型。与引理1.6.3进行比较。

1.9.18 示例：考虑在示例1.9.15中出现的形式 Cons $\left({ }_{-}, \mathbf{z}\right)$，我们有


$$
\begin{aligned}
& \llbracket \mathrm{T}: \operatorname{Cons}(-\mathrm{z}) \rrbracket \\
\equiv & \exists \mathrm{Z}_{1} \cdot\left(\llbracket \mathrm{Z}_{1} \rightarrow \mathrm{T}: \text { Cons } \rrbracket \wedge \llbracket \mathrm{Z}_{1}:(, \mathrm{z}) \rrbracket\right) \\
\equiv & \exists \mathrm{Z}_{1} \cdot\left(\mathrm{Z}_{1} \rightarrow \mathrm{T} \preceq \text { Cons } \wedge \exists \mathrm{Z}_{2} \mathrm{Z}_{3} \cdot\left(\llbracket \mathrm{Z}_{2} \rightarrow \mathrm{Z}_{3} \rightarrow \mathrm{Z}_{1}:(\cdot, \cdot) \rrbracket \wedge \llbracket \mathrm{Z}_{2}: \_\rrbracket \wedge \llbracket \mathrm{Z}_{3}: \mathrm{z} \rrbracket\right)\right) \\
\equiv & \exists \mathrm{Z}_{1} \mathrm{Z}_{2} \mathrm{Z}_{3} \cdot\left(\mathrm{Z}_{1} \rightarrow \mathrm{T} \preceq \operatorname{Cons} \wedge \mathrm{Z}_{2} \rightarrow \mathrm{Z}_{3} \rightarrow \mathrm{Z}_{1} \preceq(\cdot, \cdot) \wedge \mathrm{Z}_{3} \preceq \mathrm{z}\right)
\end{aligned}
$$

其中 $\mathrm{Z}_{1}, \mathrm{Z}_{2}, \mathrm{Z}_{3}$ 对 $\mathrm{T}$ 而言是新的。现在让我们将这个约束放在初始环境的范围内，该环境为构造器 Cons 和 $(\cdot, \cdot)$ 分配类型方案，并且在将 $z$ 绑定到某种类型 $\mathrm{T}^{\prime}$ 的范围内。

We find

$$
\begin{aligned}
& \text { let } \Gamma_{0} \text { in let } \mathrm{z}: \mathrm{T}^{\prime} \text { in } \llbracket \mathrm{T}: \text { Cons }(, \mathrm{z}) \rrbracket \\
\equiv & \exists \mathrm{Z}_{1} \mathrm{Z}_{2} \mathrm{Z}_{3} \cdot\left(\exists \mathrm{X} \cdot\left(\mathrm{Z}_{1} \rightarrow \mathrm{T} \leq \mathrm{X} \times \text { list } \mathrm{X} \rightarrow \text { list } \mathrm{X}\right) \wedge\right. \\
\equiv & \left.\exists \mathrm{Y}_{1} \mathrm{Y}_{2} \cdot\left(\mathrm{Z}_{2} \rightarrow \mathrm{Z}_{3} \rightarrow \mathrm{Z}_{1} \leq \mathrm{Y}_{1} \rightarrow \mathrm{Y}_{2} \rightarrow \mathrm{Y}_{1} \times \mathrm{Y}_{2}\right) \wedge \mathrm{Z}_{3} \leq \mathrm{T}^{\prime}\right) \\
\equiv & \exists \mathrm{X} \cdot\left(\mathrm{T} \leq \text { list } \mathrm{X} \wedge \text { list } \mathrm{X} \leq \mathrm{T}^{\prime}\right)
\end{aligned}
$$

最终简化主要依赖于C-ARROw、相应产品的规则以及C-ExTrans，并将其留给读者作为一个练习。因此，该约束表明模式匹配具有类型列表X的值（等价地，其类型T是列表X的子类型的值），对于某些未确定的元素类型X，并将z绑定到类型为列表X的值（等价地，其类型$T^{\prime}$是列表X的超类型的值）。

上述例子似乎表明，模式生成的约束规则是有一定道理的。然而，细心的读者可能会对第三条规则感到有些困惑，与表达式的情况相比，它颠倒了子类型的方向，却没有颠倒实例化的方向。实际上，为了使这条规则有意义且可靠，我们必须制定一个关于分配给构造器的类型方案的要求。

1.9.19 定义：构造函数 $c$ 可逆当且仅当，当 $\vec{X}$ 和 $\vec{X}^{\prime}$ 长度为 $a(\mathrm{c})$ 时，约束 $\Gamma_{0}$ 使得 $\left(\overrightarrow{\mathrm{X}}^{\prime} \rightarrow \mathrm{T} \preceq \mathrm{c} \wedge \mathrm{c} \preceq \overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}\right)$ 推出 $\overrightarrow{\mathrm{X}} \leq \overrightarrow{\mathrm{X}}^{\prime}$。在以下内容中，我们假设模式仅包含可逆构造函数。

直观地说，当$\mathrm{c}$是可逆的，就有可能从$c \mathrm{v}_{1} \ldots \mathrm{v}_{k}$的类型恢复每个$\mathrm{v}_{i}$的类型，这是模式匹配得以可能的关键属性。请注意，如果$\Gamma_{0}(\mathrm{c})$是单态的，那么$\mathrm{c}$就是可逆的。以下引理识别了另一类重要的可逆构造器。

1.9.20 引理：代数数据类型的构造函数是可逆的。

证明：设 $\mathrm{c}$ 是由代数数据类型 $D$ 的定义引入的构造器。设 $k=a(\mathrm{c})$。那么，类型方案 $\Gamma_{0}(\mathrm{c})$ 具有以下形式 $\forall \overline{\mathrm{Y}} . \overrightarrow{\mathrm{T}} \rightarrow \mathrm{D} \overrightarrow{\mathrm{Y}}$，其中 $\overrightarrow{\mathrm{Y}}$ 是定义的参数，$\overrightarrow{\mathrm{T}}$ 是长度为 $k$ 的向量，包含定义的一些组件。（更准确地说，在变体类型的情况下，$\overrightarrow{\mathrm{T}}$ 只包含一个组件，在记录类型的情况下，包含所有组件。）设 $\overrightarrow{\mathrm{X}}$ 和 $\overrightarrow{\mathrm{X}}^{\prime}$ 的长度为 $k$。设 $\forall \overrightarrow{\mathrm{Y}}_{1} \cdot \overrightarrow{\mathrm{T}}_{1} \rightarrow \mathrm{D} \overrightarrow{\mathrm{Y}}_{1}$ 和 $\forall \overline{\mathrm{Y}}_{2} \cdot \overrightarrow{\mathrm{T}}_{2} \rightarrow \mathrm{D} \overrightarrow{\mathrm{Y}}_{2}$ 是类型方案 $\Gamma_{0}(\mathrm{c})$ 的两个 $\alpha$-等价形式，且 $\overline{\mathrm{Y}}_{1} \# \overline{\mathrm{Y}}_{2}$ 和 $\overline{\mathrm{Y}}_{1} \overline{\mathrm{Y}}_{2} \# \operatorname{ftv}\left(\overline{\mathrm{X}}, \overline{\mathrm{X}}^{\prime}, \mathrm{T}\right)$。根据定义，约束 let $\Gamma_{0}$ in $\left(\overrightarrow{\mathrm{X}}^{\prime} \rightarrow \mathrm{T} \preceq \mathrm{c} \wedge \mathrm{c} \preceq \overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}\right)$ 等价于 $\overrightarrow{\mathrm{X}}^{\prime} \rightarrow \mathrm{T} \prec \Gamma_{0}(\mathrm{c}) \wedge \Gamma_{0}(\mathrm{c}) \prec \overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}$，即 $\exists \overline{\mathrm{Y}}_{1} \cdot\left(\overrightarrow{\mathrm{X}}^{\prime} \rightarrow \mathrm{T} \leq \overrightarrow{\mathrm{T}}_{1} \rightarrow \mathrm{D} \overrightarrow{\mathrm{Y}}_{1}\right) \wedge \exists \overline{\mathrm{Y}}_{2} \cdot\left(\overrightarrow{\mathrm{T}}_{2} \rightarrow \mathrm{D} \overrightarrow{\mathrm{Y}}_{2} \leq \overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}\right)$。根据 C-ExAND 和 CARRow，可以写成 $\exists \bar{Y}_{1} \bar{Y}_{2} \cdot\left(D \vec{Y}_{2} \leq T \leq D \vec{Y}_{1} \wedge \vec{X} \leq \vec{T}_{2} \wedge \vec{T}_{1} \leq \vec{X}^{\prime}\right)$。现在，根据定义 1.9.8，$D \overrightarrow{\mathrm{Y}}_{2} \leq \mathrm{D} \overrightarrow{\mathrm{Y}}_{1}$ 意味着 $\overrightarrow{\mathrm{T}}_{2} \leq \overrightarrow{\mathrm{T}}_{1}$，因此前面的约束蕴含着 $\exists \bar{Y}_{1} \overline{\mathrm{Y}}_{2} \cdot\left(\overrightarrow{\mathrm{X}} \leq \overrightarrow{\mathrm{X}}^{\prime}\right)$，即 $\overrightarrow{\mathrm{X}} \leq \overrightarrow{\mathrm{X}}^{\prime}$。

与非可逆构造器相关的一个重要类别是与存在类型定义相关的（第118页），其中类型方案$\Gamma_{0}(c)$中的并非所有量词都是类型构造器D的参数。例如，在定义$\mathrm{D} \approx \ell: \exists \mathrm{X} . \mathrm{X}$下，与$\ell$相关的类型方案是$\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{D}$。然后，很容易检查出$\ell$是不可逆的。这反映了不可能从$\ell \mathrm{v}$的类型（在任何情况下必须是$D$）恢复$\mathrm{v}$的类型的事实，并解释了为什么存在类型需要特殊处理。

我们现在准备好将一个约束生成规则与匹配构造关联起来。它在图1-15的下方给出。在规则的右侧，我们用$\overrightarrow{\mathbf{z}}_{i}$表示由模式$\mathrm{p}_{i}$绑定的程序变量，我们用$\overrightarrow{\mathrm{X}}_{i}$表示相同长度的类型变量向量。类型变量$\mathrm{X} \overline{\mathrm{X}}_{i}$必须有种类$\star$，必须是成对不同的，并且不得在规则左侧自由出现。现在让我们解释这个规则。它的右侧是一个合取（逻辑与），其中每个合取处理匹配构造的一个子句，要求在关于模式$\mathrm{p}_{i}$绑定的程序变量$\vec{z}_{i}$的某些假设下，$t_{i}$具有类型$T$。剩下要解释的是这些假设是如何构建的。首先，就像在let构造的情况下一样，我们召唤一个新鲜类型变量$\mathrm{X}$并产生$\llbracket \mathrm{t}: \mathrm{x} \rrbracket$，这是确保$t$具有类型$X$的最不具体的约束。然后，反映操作语义，将（由）$t$产生的值输入到模式$\mathrm{p}_{i}$中，我们将类型$\mathrm{X}$输入到$\mathrm{p}_{i}$并产生 let $\overrightarrow{\mathrm{z}}_{i}: \overrightarrow{\mathrm{X}}_{i}$ in $\llbracket \mathrm{X}: \mathrm{p}_{i} \rrbracket$，这是一个确保$\overrightarrow{\mathrm{X}}_{i}$是程序变量$\vec{z}_{i}$的正确类型假设向量的约束（参见示例1.9.18）。这解释了为什么我们可以在$\left(\vec{z}_{i}: \overrightarrow{\mathrm{x}}_{i}\right)$的作用域内放置$\llbracket \mathrm{T}: \mathrm{t}_{i} \rrbracket$。还需要指出的是，就像在let构造的情况下一样，将地面类型分配给$\mathrm{X} \overline{\mathrm{X}}_{i}$的每一个赋值，只要满足约束$\llbracket \mathrm{t}: \mathrm{X} \rrbracket \wedge$ let $\overrightarrow{\mathrm{z}}_{i}: \overrightarrow{\mathrm{X}}_{i}$ in $\llbracket \mathrm{X}: \mathrm{p}_{i} \rrbracket$都是可接受的，因此普遍量化这些类型变量是有效的。这允许程序变量$\vec{z}_{i}$在$t$本身具有多态类型时接收多态类型方案。

1.9.21 练习 [$\star$, 推荐]：我们之前建议将 let $\mathrm{z}=\mathrm{t}_{1}$ in $\mathrm{t}_{2}$ 视为 match $\mathrm{t}_{1}$ with $\mathrm{z} . \mathrm{t}_{2}$ 的语法糖，并证明了操作语义验证了这一观点。检查从类型的角度来看这也是否有效。

匹配约束生成规则，如果按字面意义实现，将取$k$份约束$\llbracket \mathrm{t}: \mathrm{x} \rrbracket$的副本。当$k$大于1时，这会损害约束生成的线性时间和空间复杂度。为了解决这个问题，可以如下修改规则：用$z \preceq x$替换每个$\llbracket t: x \rrbracket$的副本，并将约束置于上下文let $z: \forall x[\llbracket t: x \rrbracket] . x$ in []中，其中$z$是一个新的程序变量。不难验证，这样修改后约束的逻辑含义并未受到影响，并且恢复了线性行为。在实践中，解决新的约束需要取类型方案$\forall x[\llbracket t: x \rrbracket] . x$的实例，这本质上需要再次复制$\llbracket t: x \rrbracket$ —— 然而，一个高效的求解器现在可以在复制它之前简化这个子约束。

以下引理是建立RMATCH主题还原的关键。它依赖于构造函数可逆的要求。

1.9.22 引理：假设 $[\mathrm{p} \mapsto \mathrm{v}]$ 已定义，并且将 $\overrightarrow{\mathrm{z}}$ 映射到 $\overrightarrow{\mathrm{w}}$，其中 $\overline{\mathbf{z}}=d p i(\mathrm{p})$。令 $\vec{z}: \vec{T}$ 是任意一个域为 $\bar{z}$ 的单态环境。那么，在 $(\llbracket \mathrm{v}: \mathrm{T} \rrbracket \wedge$ 令 $\overrightarrow{\mathrm{z}}: \overrightarrow{\mathrm{T}}$ 在 $\llbracket \mathrm{T}: \mathrm{p} \rrbracket)$ 推导出令 $\Gamma_{0}$ 在 $\llbracket \overrightarrow{\mathrm{w}}: \overrightarrow{\mathrm{T}} \rrbracket$。

我们现在证明，通过对ML-演算进行模式匹配扩展，其具有主题还原性质。我们仅声明R-MATCH保持类型不变，并将涉及到匹配构造的求值上下文的新子情况R-CONTEXT留给读者。为了使这个子情况成功，必须将值限制（定义1.7.7）扩展到要求所有常量具有纯语义，或者所有匹配构造实际上都是形式match v with $(p_i \cdot t_i)_{i=1}^{k}$。

### 1.9.23 定理 [主题简化]：(R-MATCH) ⊆ (≤)

1.9.24练习 $[\star \star \star, \nrightarrow]$ ：为了简化，我们从模式语法中省略了生产引用 $p$ 。模式引用 $p$ 与每个内存位置匹配，其内容（相对于当前存储）与p匹配。确定为了适应这个新的产生式，之前的定义和证明必须如何扩展。

进度属性在一般情况下并不成立：例如，匹配Nil与(Cons z.z)是类型正确的（具有类型 $\forall$ X.X），但是却陷入了停滞。在实际的ML编程语言实现中，这样的错误是动态检测到的。这可以被认为是ML类型系统的一个弱点。然而幸运的是，通常可以静态地证明某个特定的匹配构造是穷尽的，不会出错。事实上，如果匹配 $\mathrm{v}$ 与 $\left(\mathrm{p}_{i} \cdot \mathrm{t}_{i}\right)_{i=1}^{k}$ 是类型正确的，那么对于每个 $i \in\{1, \ldots, k\}$，约束 let $\Gamma_{0}$ in $\left(\llbracket \mathrm{v}: \mathrm{X} \rrbracket \wedge \exists \overline{\mathrm{X}}\right.$. let $\overrightarrow{\mathrm{z}}_{i}: \overrightarrow{\mathrm{X}}$ in $\left.\llbracket \mathrm{X}: \mathrm{p}_{i} \rrbracket\right)$，其中 $\overline{\mathrm{z}}_{i}$ 是由 $\mathrm{p}_{i}$ 绑定的程序变量，必须是可满足的；即，$\mathrm{v}$ 必须具有对 $\mathrm{p}_{i}$ 可接受输入的某种类型。这个事实提供了关于 $\mathrm{v}$ 的信息，从中可能可以推导出 $\mathrm{v}$ 必须匹配其中一个模式 $\mathrm{p}_{i}$。

1.9.25 示例：设 $k=2, \mathrm{p}_{1}=\mathrm{Nil}$，以及 $\mathrm{p}_{2}=$ Cons $\left(\mathbf{z}_{1}, \mathbf{z}_{2}\right)$。那么，约束条件让 $\Gamma_{0}$ 在 $\exists \overline{\mathrm{X}}$ 中。让 $\overrightarrow{\mathrm{z}}_{i}: \overrightarrow{\mathrm{X}}$ 在 $\llbracket \mathrm{X}: \mathrm{p}_{i} \rrbracket$ 中，对于 $i \in\{1,2\}$，简化后（当 $i=2$ 时）都等价于 $\exists \mathrm{Z}$。 $\mathrm{X} \leq$ list $\mathrm{Z}$。因为类型构造器 list 是孤立的，每个类型为 $\mathrm{X}$ 的闭合值 $\mathrm{v}$ 满足这个约束
必须是对 $\mathrm{Nil}$ 或 Cons 的应用。如果是后者，因为 Cons 有类型 $\forall \mathrm{X} . \mathrm{X} \times$ list $\mathrm{X} \rightarrow$ list $\mathrm{X}$，并且因为类型构造器 $\times$ 是孤立的，Cons 的参数必须是一个对。我们得出结论，$v$ 必须匹配 $\mathrm{p}_{1}$ 或 $\mathrm{p}_{2}$ 中的一个，这保证了这个匹配构造是详尽的，其评估不会出错。

本章的范围无法详尽地介绍检查详尽性的内容。读者可以参考（Sekar, Ramesh, 和 Ramakrishnan, 1995；Le Fessant 和 Maranget, 2001）。

## Type annotations

到目前为止，我们对一种非常纯粹且极端的类型推断形式很感兴趣。实际上，在ML-演算中，表达式完全不包含显式的类型信息：它们完全是被推断出来的。然而，在实践中，在表达式中插入类型注解往往是有用的，因为它们提供了一种由机器检查的文档形式。当试图追踪类型错误的原因时，类型注解也很有帮助：通过向类型检查器提供（假设）正确的类型信息，你更有可能找到接近实际编程错误处的类型不一致问题。

当类型注解被允许包含类型变量时，人们必须非常小心地考虑这些变量在程序的哪个点（程序点）以及如何（存在性地或普遍性地）绑定。实际上，如果不解决这些问题，就无法精确地定义类型注解的含义。在以下内容中，我们首先解释如何引入局部和存在性地绑定类型变量的类型注解。我们展示，通过添加这种受限的类型注解来扩展ML-计算 calculus只是一个引入新常量的简单问题。然后，我们转向更一般的情况，即类型变量可以在任何程序点明确地存在性地引入。我们将普遍绑定类型变量的讨论推迟到第1.10节。

让一个局部存在类型注解 $\exists \overline{\mathrm{X}}$。$\mathrm{T}$ 是一个由类型变量集合 $\overline{\mathrm{X}}$ 和一个类型 $\mathrm{T}$ 组成的二元组，其中 $\mathrm{T}$ 的种类为 $\star$，$\overline{\mathrm{X}}$ 在 $\mathrm{T}$ 中被视为绑定，并且 $\overline{\mathrm{X}}$ 包含 $f t v(\mathrm{~T})$。对于每一个这样的注解，我们引入一个新的一元析构器 $(\cdot: \exists \overline{\mathrm{X}} . \mathrm{T})$。这样的定义之所以有效，仅仅是因为类型注解必须是封闭的，即不含有任何自由类型变量。我们用 $(t: \exists \bar{X} . T)$ 来表示应用 $((\cdot: \exists \bar{X} . T)) t$。由于类型注解不会影响程序的含义，这个新的析构器具有身份语义：

$$
(\mathrm{v}: \exists \overline{\mathrm{X}} . \mathrm{T}) \xrightarrow{\delta} \mathrm{v}
$$

(R-AnNotation)

然而，它的类型方案并不是身份类型，即 $\forall X . X \rightarrow X$ ：相反，它更具体，这样对表达式的注解限制了其类型。实际上，
我们将初始环境 $\Gamma_{0}$ 扩展到包含以下绑定：

$$
(\cdot: \exists \overline{\mathrm{X}} . \mathrm{T}): \forall \overline{\mathrm{X}} . \mathrm{T} \rightarrow \mathrm{T}
$$

1.9.26 练习 [ $\star$ ]：检查 $\forall \overline{\mathrm{X}} . \mathrm{T} \rightarrow \mathrm{T}$ 是否是根据Damas和Milner的说法，是 $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$ 的一个实例，即前者是通过练习1.2.23中给出的规则DM-INST'从后者得到的。这是否允许我们论证分配给 $(\cdot: \exists \overline{\mathrm{X}} . \mathrm{T})$ 的类型方案是合理的？检查以上定义是否符合定义1.7.6的要求。

尽管插入类型注解不会改变程序的语义，但它确实会影响约束生成，从而影响类型推断。我们让读者验证，假设 $\overline{\mathrm{X}} \# f t v\left(\mathrm{t}, \mathrm{T}^{\prime}\right)$，以下派生的约束生成规则成立：

$$
\text { let } \Gamma_{0} \text { in } \llbracket(\mathrm{t}: \exists \overline{\mathrm{X}} . \mathrm{T}): \mathrm{T}^{\prime} \rrbracket \equiv \text { let } \Gamma_{0} \text { in } \exists \overline{\mathrm{X}} \cdot\left(\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{T}^{\prime}\right)
$$

到目前为止，表达式不能有自由类型变量，所以假设 $\overline{\mathrm{x}}$ \# $f t v(\mathrm{t})$ 可能看起来是多余的。然而，我们很快将允许表达式中包含带有自由类型变量的类型注释，因此我们更愿意现在就明确这个条件。根据这个规则，类型注释的效果是强制表达式 $t$ 具有某种类型变量 $\overline{\mathrm{X}}$ 选择下的类型 $\mathrm{T}$。与具有子类型的类型系统中的通常情况一样，表达式的最终类型 $\mathrm{T}^{\prime}$ 随后可以是这个特定实例 $\mathrm{T}$ 的任意超类型。当子类型被解释为等式时，$\mathrm{T}^{\prime}$ 和 $\mathrm{T}$ 通过约束被等同起来，因此这个约束生成规则可以理解为：( $\mathrm{t}: \exists \overline{\mathrm{X}} \mathrm{T}$ ) 的有效类型必须是某种类型变量 $\overline{\mathrm{x}}$ 选择下的形式 $\mathrm{T}$。

1.9.27 示例：在将整数扩展到DM中，表达式（ $\lambda z . z:$ int $\rightarrow$ int）具有最一般的类型int $\rightarrow$ int，尽管底层的恒等函数具有最一般的类型 $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$，因此注解限制了其类型。表达式 $(\lambda z . z \hat{+} \hat{1}: \exists X . X \rightarrow X)$ 的类型为int $\rightarrow$ int，这也是底层函数的最一般类型，所以在这种情况下注解仅作为文档存在。请注意，类型变量 $\mathrm{X}$ 通过约束求解器实例化为int。表达式 $(\lambda z .(z \hat{1}): \exists X . X \rightarrow$ int) 的类型为 (int $\rightarrow$ int) $\rightarrow$ int，因为底层函数的类型为 (int $\rightarrow \mathrm{Y}) \rightarrow \mathrm{Y}$，通过将 $\mathrm{X}$ 实例化为int $\rightarrow$ int 和 $\mathrm{Y}$ 实例化为int，它与 $\mathrm{X} \rightarrow$ int 成功统一。最后，表达式 ( $\lambda \mathrm{z} \cdot(\mathrm{z} \hat{1}): \exists \mathrm{X}$.int $\rightarrow \mathrm{X}$ ) 类型错误，尽管底层表达式类型正确，因为方程 (int $\rightarrow \mathrm{Y}) \rightarrow \mathrm{Y}=$ int $\rightarrow \mathrm{X}$ 是无法满足的。

1.9.28 示例：在带有对的DM扩展中，表达式 $\lambda z_{1} \cdot \lambda z_{2} \cdot\left(\left(z_{1}:\right.\right.$ $\left.\exists X . X),\left(z_{2}: \exists X . X\right)\right)$ 的最一般类型是 $\forall X Y . X \rightarrow Y \rightarrow X \times Y$。换句话说，两个出现的 $X$ 并不表示同一类型。实际上，完全可以写成 $\lambda z_{1} \cdot \lambda z_{2} \cdot\left(\left(z_{1}: \exists X . X\right),\left(z_{2}: \exists Y . Y\right)\right)$。如果希望 $z_{1}$ 和 $z_{2}$ 接收相同类型，必须提升类型注释并将它们合并到对构造函数上方，如下所示：$\lambda z_{1} \cdot \lambda z_{2} \cdot\left(\left(z_{1}, z_{2}\right): \exists X . X \times X\right)$。在这个过程中，类型构造函数 $X$ 出现在注释中，导致其大小增加。

上述示例揭示了这种类型注释风格的一个限制：通过要求每个类型注释都是闭合的，我们失去了两个独立注释共享一个类型变量的能力。然而，有时这种特性是可取的。如果希望在代码中远距离共享的两个注释，将其提升并合并为一个注释可能会显得不协调；因此，有时确实需要更多的表达力。

因此，我们开始考虑更一般的类型注释，形式为 $(\mathrm{t}: \mathrm{T})$，其中 $\mathrm{T}$ 的种类为 $\star$，并且在 $\mathrm{T}$ 中出现的类型变量被认为是自由的，这样不同的类型注释可以引用共享的类型变量。然而，为了使这个想法有意义，仍然需要指定这些类型变量绑定在哪里。我们使用形式为 $\exists \overline{\mathrm{X}}$.t 的表达式来进行指定。这样的表达式在表达式 $t$ 中绑定了类型变量 $\overline{\mathrm{X}}$，使得在 $t$ 中的类型注释内部所有自由出现的 $X$（其中 $X \in \bar{X}$）都代表相同的类型。因此，我们将简单的类型注释构造 $(\cdot: \exists \overline{\mathrm{X}}$.T) 分解为两个更基本的组成部分，即存在类型变量引入 $\exists \overline{\mathrm{X}} \cdot$ 和类型约束 $(\cdot: \mathrm{T})$。请注意，两者都是新的表达式形式；它们不能通过向演算中添加新常数来编码，因为不可能为它们分配闭合类型方案。

技术上，允许表达式中包含类型变量需要谨慎处理。几个约束生成规则使用辅助类型变量，这些变量在生成的约束中被绑定。这些类型变量可以以任意方式选择，只要它们不出现在规则的左侧——这是为了避免意外捕获的附加条件。到目前为止，这个附加条件可以解读为：用来形成约束 $\llbracket t: T \rrbracket$ 的辅助类型变量不得在 $\mathrm{T}$ 中自由出现。现在，由于类型注解可能包含自由类型变量，附加条件变为：用来形成 $\llbracket \mathrm{t}: \mathrm{T} \rrbracket$ 的辅助类型变量不得在 $\mathrm{t}$ 或 $\mathrm{T}$ 中自由出现。

考虑到这个扩展的附加条件，我们原始的约束生成规则保持不变。我们添加了两条新规则来描述新的表达式形式如何影响约束生成：

$$
\begin{aligned}
\llbracket \exists \overline{\mathrm{X}} . \mathrm{t}: \mathrm{T} \rrbracket & =\exists \overline{\mathrm{X}} \cdot \llbracket \mathrm{t}: \mathrm{T} \rrbracket & \text { provided } \overline{\mathrm{X}} \# \mathrm{ftv}(\mathrm{T}) \\
\llbracket(\mathrm{t}: \mathrm{T}): \mathrm{T}^{\prime} \rrbracket & =\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{T}^{\prime} &
\end{aligned}
$$

这些规则的效果很简单。构造 $\exists \bar{x}$.t 是向约束生成器指示，类型变量 $\overline{\mathrm{X}}$，可能在 $t$ 内部的类型注释中自由出现，此时应存在性地绑定。侧条件 $\overline{\mathrm{X}}$ \# $f t v(\mathrm{~T})$ 确保在生成的约束中对 $\overline{\mathrm{X}}$ 进行量化不会捕获预期类型 T 中的类型变量。它总是可以通过表达式 $\exists \overline{\mathrm{X}}$.t 的 $\alpha$-转换来满足。构造 ( $\mathrm{t}: \mathrm{T}$ ) 是向约束生成器指示表达式 $t$ 应该具有类型 $\mathrm{T}$，并通过生成子约束 $\llbracket t: T \rrbracket$ 来这样处理。表达式的类型可能是 $\mathrm{T}$ 的任意超类型，因此有辅助约束 $\mathrm{T} \leq \mathrm{T}^{\prime}$。

1.9.29 示例：在通过成对扩展的DM中，表达式 $\lambda z_{1} \cdot \lambda z_{2} \cdot \exists x .\left(\left(z_{1}\right.\right.$ : $\left.\mathrm{X}),\left(\mathrm{z}_{2}: \mathrm{X}\right)\right)$ 具有最一般的类型 $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X} \rightarrow \mathrm{X} \times \mathrm{X}$。实际上，为这个表达式生成的约束包含了模式 $\exists x .\left(\llbracket z_{1}: x \rrbracket \wedge \llbracket z_{2}: x \rrbracket \wedge \ldots\right)$，这导致 $z_{1}$ 和 $z_{2}$ 接收到相同类型。请注意，这种风格比示例1.9.28中采用的风格更灵活，在示例1.9.28中，我们被迫使用单一、庞大的类型注释来表达这个共享约束。

1.9.30 备注：实际上，类型变量通常在类型检查器的堆中作为一个内存单元表示。因此，不能说源代码包含类型变量；更准确地说，它包含的是旨在代表类型变量的名字。让我们用 $X$ 来表示这样的名字，用 $T$ 来表示由类型构造器和名字组成的类型，而不是由类型构造器和类型变量组成的类型。那么，我们新的表达式形式实际上是 $\exists \bar{X}$.t 和 ( $\mathrm{t}: T$ )。当约束生成器进入一个引入形式 $\exists \bar{X}$.t 的作用域时，它会分配一个由新类型变量 $\overline{\mathrm{X}}$ 组成的向量，并用绑定 $\bar{X} \mapsto \overline{\mathrm{X}}$ 来增强内部环境。因为类型变量是新的，所以上面第一个约束生成规则的附加条件自动满足。当约束生成器找到一个类型注解 ( $t: T$ ) 时，它会查阅内部环境来将类型注解 $T$ 翻译成一个内部类型 $\mathrm{T}$ —— 如果 $T$ 包含一个不在作用域内的名字，这个操作会失败 —— 并应用上面第二个约束生成规则。

1.9.31练习 $[\star \star, \nrightarrow]$ ：设 $\overline{\mathrm{X}} \supseteq f t v(\mathrm{~T})$ 且 $\overline{\mathrm{X}} \# f t v(\mathrm{t})$ 。检查约束 $\llbracket(\mathrm{t}: \exists \overline{\mathrm{X}} . \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ 和 $\llbracket \exists \overline{\mathrm{X}} .(\mathrm{t}: \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ 是否等价。换句话说，前面引入的局部类型注释可以用上面描述的更复杂构造来表达。

1.9.32 练习 $[\star \star, \nrightarrow]$ ：赋予我们新型类型注解构造语义的一种方式是在执行之前完全擦除它们。给出一个归纳定义 $\lfloor t\rfloor$，即通过移除表达式 $t$ 中的所有类型注解构造所得到的表达式。检查 $\llbracket t: T \rrbracket$ 是否意味着 $\llbracket\lfloor t\rfloor$ : $\mathrm{T} \rrbracket$ 并解释为什么这足以确保类型的健全性。

研究存在量化类型变量明确引入与let多态性之间的相互作用是很有趣的。它们之间的交互源自在$C_{2}$中的约束let $\mathrm{z}: \forall \overline{\mathrm{x}}\left[\exists \mathrm{X} . C_{1}\right] . \mathrm{T}$ 与 $\exists$ x.let $\mathrm{z}: \forall \overline{\mathrm{x}}\left[C_{1}\right] . \mathrm{T}$ 之间的区别，这在例子1.3.28中有所解释。在前一个约束中，$C_{2}$内部$\mathrm{z}$的每一次自由出现都会取$\exists \mathrm{x} . C_{1}$的一个副本，从而创建其自己的X的新鲜副本。而在后一个约束中，$C_{2}$内部的每一次$\mathrm{z}$的自由出现都会产生$C_{1}$的一个副本。所有这样的副本都引用$\mathrm{X}$，因为它的量化符没有被复制。在前一种情况下，可以说分配给$z$的类型方案关于$\mathrm{X}$是多态的，而在后一种情况下它是单态的。因此，源代码中类型变量引入表达式相对于let绑定的位置是有意义的：在let构造之外引入类型变量可以防止它被泛化。

1.9.33 示例：在DM中扩展了整数和布尔值的情况下，程序 let $f=$ $\exists X . \lambda z .(z: X)$ in (f $0, f$ true) 是类型正确的。实际上，分配给 $f$ 的类型方案是 $\forall X . X \rightarrow X$。然而，程序 $\exists X$.let $f=\lambda z .(z: X)$ in ($f 0, f$ true) 是类型错误的。实际上，分配给 $f$ 的类型方案是 $X \rightarrow X$；然后，没有任何 $X$ 的值满足与应用程序 $f 0$ 和 $f$ true 相关联的约束。后者的行为在Objective Caml中观察到，在那里类型变量在表达式的外部最顶层隐式引入：

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-105.jpg?height=89&width=995&top_left_y=1139&top_left_x=620)

关于标准ML、Objective Caml和Haskell中类型注释的处理，更多细节请参见第113页。

1.9.34 练习 $[\star, \nrightarrow]$ ：确定在示例1.9.33中的两个程序生成了哪些约束。检查前一个程序确实类型正确，而后一个程序类型错误。

## Recursive types

我们已经证明了，将$\operatorname{HM}(X)$与仅含等式的语法模型进行特化可以得到$\operatorname{HM}(=)$，这是Damas和Milner类型系统的一种基于约束的形式化。类似地，也可以将$\operatorname{HM}(X)$与仅含等式的自由正则树模型进行特化，得到一个可以被视为Damas和Milner类型纪律扩展的基于约束的类型系统，其中包括递归类型。这种递归类型有时被称为等价递归，因为此时循环等式（如$\mathrm{X}=\mathrm{X} \rightarrow \mathrm{X}$）是可以满足的。我们关于类型推断和类型安全性的定理，这些定理与模型无关，仍然有效。第1.8节中描述的约束求解器可以用于仅含等式的自由正则树模型中：与语法情况唯一的不同在于不再执行出现检查。

请注意，尽管地面类型是规则的，但类型仍然是有限的对象：它们的语法保持不变。通常用来描述递归类型的 $\mu$ 符号可以使用类型方程来模拟：例如，在基于约束的方法中，记法 $\mu \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$ 对应于类型方案 $\forall x[X=X \rightarrow X]$。$\mathrm{X}$。

尽管如上所述，递归类型是免费的，但它们并没有被基于ML类型系统的主流编程语言所采用。原因是实用性的：经验表明，在递归类型的存在下，许多无意义的表达式都是类型正确的，而在没有递归类型的情况下则不是。因此，表达能力的提高被许多编程错误比原来可能更晚被发现的事实所抵消。例如，考虑以下的OCaml会话：

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-106.jpg?height=202&width=956&top_left_y=862&top_left_x=602)

这种荒谬的map变体基本上是无用的，但类型却很准确。在我们的表示法中，其主要类型方案是 $\forall \mathrm{XYZ}[\mathrm{Y}=$ 列表 $\mathrm{Y} \wedge \mathrm{Z}=$ 列表 $\mathrm{Z}] . \mathrm{X} \rightarrow \mathrm{Y} \rightarrow \mathrm{Z}$。在没有递归类型的情况下，它是类型不正确的，因为此时约束 $Y=$ 列表 $\mathrm{Y} \wedge \mathrm{Z}=$ 列表 $\mathrm{Z}$ 是错误的。

递归类型的需求通常被语言中提供的代数数据类型所抑制，这些代数数据类型提供了同递归类型。然而，在一些情况下，它们仍然是必要的，比如在Objective Caml的对象导向扩展（Rémy和Vouillon，1998年）中，递归对象类型通常是被推断出来的。为了允许递归对象类型同时拒绝上述map变体，Objective Caml的约束求解器实现了一个选择性的出现检查，它禁止循环，除非它们涉及到与对象关联的类型构造器 $\langle\cdot\rangle$。相应的模型是一个树模型，其中每条从树向下延伸的无限路径都必须无限次地遇到类型构造器 $\langle\cdot\rangle$。

### 1.10 约束中的全称量化

迄今为止研究的约束逻辑允许一组变量 $\overline{\mathrm{X}}$ 在公式 $C$ 内存在量词化。得到的公式 $\exists \overline{\mathrm{x}}$. $C$ 具有其标准含义：它要求 $C$ 对某些 $\overline{\mathrm{X}}$ 成立。然而，我们目前无法要求公式 $C$ 对所有 $\overline{\mathrm{X}}$ 成立。我们能否用全称量化来扩展我们的逻辑呢？如果是，这种扩展在类型推断方面提供哪些新的可能性？本节提出对这些问题的某些答案。

值得注意的是，尽管类型方案的标准表示法涉及符号$\forall$，但类型方案的引入和实例化约束并不允许编码全称量化。实际上，类型方案中的全称量词与约束中的存在量词非常相似：这一点例如由定义1.3.3和C-LETEx提出。

## Constraints

我们以下扩展约束的语法：

$$
C::=\ldots \mid \forall \overline{\mathrm{x}} . C
$$

普遍量化的变量通常被称为刚性的，而存在量化的变量被称为柔性的。对约束的逻辑解释（图1-5）如下扩展：

$$
\begin{gather*}
\forall \vec{t} \quad \phi[\overrightarrow{\mathrm{x}} \mapsto \vec{t}] \vdash \operatorname{def} \Gamma \text { in } C \\
\overline{\mathrm{x}} \# f t v(\Gamma)  \tag{CM-ForALL}\\
\hline \vdash \operatorname{def} \Gamma \text { in } \forall \overline{\mathrm{x}} . C
\end{gather*}
$$

我们让读者验证，这一添加并没有影响到1.3节中建立的任何结果。此外，扩展的约束语言具有以下性质。

1.10.1 引理：对于所有 $\overline{\mathrm{x}}$ ，$C \Vdash C$ 。反之，如果 $\overline{\mathrm{x}} \# \operatorname{ftv}(C)$ ，那么 $C \Vdash \forall \overline{\mathrm{x}} . C$ 。

1.10.2 引理：$\overline{\mathrm{X}} \# \operatorname{ftv}(C_{2})$ 意味着 $\forall \overline{\mathrm{x}} .(C_{1} \wedge C_{2}) \equiv (\forall \overline{\mathrm{x}} . C_{1}) \wedge C_{2}$.

1.10.3 引理：对于所有$\overline{\mathrm{X}}$和$\overline{\mathrm{Y}}$，$C$等价于对于所有$\overline{\mathrm{X}} \overline{\mathrm{Y}}$，$C$。

1.10.4 引理：设 $\overline{\mathrm{x}} \# \overline{\mathrm{Y}}$。那么，$\exists \overline{\mathrm{x}} . \forall \overline{\mathrm{Y}} . C$ 意味着 $\forall \overline{\mathrm{Y}} . \exists \overline{\mathrm{X}} . C$。反之，如果 $\exists \overline{\mathrm{Y}} . C$ 决定 $\overline{\mathrm{X}}$，那么 $\forall \overline{\mathrm{Y}} . \exists \overline{\mathrm{X}} . C$ 意味着 $\exists \overline{\mathrm{X}} . \forall \overline{\mathrm{Y}} . C$。

约束求解##

我们简要说明如何扩展第1.8节中描述的约束求解器，以支持全称量化。（因此，我们再次假设一个仅包含等式的自由树模型。）在方程和存在量词、全称量词的情况下进行的约束求解称为混合前缀下的统一。它是关于树上的第一阶等式理论的决策问题的一个特例；例如参见（Comon和Lescanne，1989年）。扩展我们的求解器是直接的：实际上，全称量词的处理转换成了。

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

## 图1-16：解决通用约束条件

实际上是出人意料地类似于let约束的那个。首先，我们用所谓的通用帧扩展堆栈的语法：

$$
S::=\ldots \mid S[\forall \overline{\mathrm{x}} . \square]
$$

因为一般来说，存在量词不能从全称量词中提升出来，规则S-Ex-1至S-Ex-4现在允许将它们提升到最近的封闭let或全称框架，如果有，否则提升到最外层。因此，在我们的堆栈机表示中，规则S-Ex-1至S-Ex-4以急切的方式应用，每个全称框架都携带一个类型变量的列表，这些变量在它之后立即存在性地绑定，而整数等级不仅计算let框架，还计算全称框架。

求解器的规格在图1-16的规则中进行了扩展。SSolve-All是一个前向规则，它发现了一个普遍约束并将其输入，创建了一个新的普遍框架来记录其存在。S-ALLEx利用引理1.10.4将存在量词从普遍框架中提升出来。它类似于S-LETALL，其实现可能依赖于相同的程序（练习1.8.8）。接下来两个规则检测失败条件。SALL-FAIL-1指出，如果刚体变量X直接或间接被自由变量Z支配，那么约束$\forall \mathrm{X} . \exists \overline{\mathrm{Y}} . U$是假的。实际上，X的值那时由Z的值确定，但是普遍量化的变量涵盖所有值，所以这是矛盾的。在这种情况下，通常说X逃出了其作用域。S-ALL-FAIL-2指出，如果X与非变量项相等，则同一约束也是假的。实际上，X的值部分确定，因为其头构造器是已知的，这再次与它的普遍地位相矛盾。最后，S-POP-ALL将当前的统一约束分解为两个组成部分$U_{1}$和$U_{2}$，其中$U_{1}$完全由旧变量组成，而$U_{2}$只约束新变量。这种分解类似于S-POP-LET执行的操作。然后，不难检查$\forall \overline{\mathrm{X}} . \exists \overline{\mathrm{Y}}$。$\left(U_{1} \wedge U_{2}\right)$等价于$U_{1}$。因此，普遍框架以及$U_{2}$都被丢弃，求解器通过检查堆栈S顶部的其余内容继续进行。

可以进一步扩展通用帧的处理，使用两个类似于S-COMPRESS和S-UNNAME的规则。实际上，这提高了求解器的效率，并使得在let帧处理和通用帧处理之间共享代码变得更加容易。

值得注意的是，就底层的统一算法而言，存在量化和普遍量化类型变量之间没有区别。该算法解决呈现给它的任何方程，而不询问它们变量的状态。导致失败的那些方程，因为一个刚性变量逃逸了它的作用域，或者与一个非变量项相等，只有在退出普遍框架时才会被检测到。或许更常见的方法是将刚性变量标记为刚性，使得统一算法在遇到两个错误条件之一时立即发出失败信号。在这种方法中，刚性变量可能只成功与自己或比自己更新的灵活变量统一。在文献中，它通常被称为Skolem构造器（Läufer和Odersky，1994；Shields和Peyton Jones，2002）。这种方法的 一种有趣的变体出现在Dowek，Hardin，Kirchner和Pfenning对（高阶）统一处理中（1995；1998年），其中灵活变量被表示为普通变量，而刚性变量则使用De Bruijn索引进行编码。

我们约束求解器的属性通过这个扩展得到了保持：有可能证明引理1.8.9、1.8.10和1.8.11仍然有效。

类型注解，继续

在1.9节中，我们引入了表达式形式（$t: \exists \overline{\mathrm{X}} . \mathrm{T}$），允许表达式$t$用带有局部和存在性绑定的自由变量$\overline{\mathrm{X}}$的类型$\mathrm{T}$进行注释。现在很自然地引入了对称的表达式形式（$\mathrm{t}: \forall \overline{\mathrm{X}} . \mathrm{T}$），其中$\mathrm{T}$具有种类$\star$，$\overline{\mathrm{X}}$在$\mathrm{T}$内绑定，并且$\overline{\mathrm{X}}$包含$f t v(\mathrm{~T})$，如前所述。其约束生成规则如下：

$$
\llbracket(\mathrm{t}: \forall \overline{\mathrm{X}} \cdot \mathrm{T}): \mathrm{T}^{\prime} \rrbracket=\forall \overline{\mathrm{X}} \cdot \llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \exists \overline{\mathrm{X}} \cdot\left(\mathrm{T} \leq \mathrm{T}^{\prime}\right) \quad \text { provided } \overline{\mathrm{X}} \# f t v\left(\mathrm{t}, \mathrm{T}^{\prime}\right)
$$

第一个连接词要求对所有$\overline{\mathrm{X}}$的值，$t$具有类型$T$。在这里，类型变量$\overline{\mathrm{X}}$按预期是普遍约束的。第二个连接词要求$\mathrm{T}^{\prime}$是普遍注解$\forall \overline{\mathrm{X}}$.T的某个实例。由于$\mathrm{T}^{\prime}$只是一个单型，似乎很难想到另一种合理的限制$\mathrm{T}^{\prime}$的方法。因此，在第二个连接词中，类型变量$\overline{\mathrm{X}}$仍然存在性约束。这使得类型注解中普遍量词的解释比存在量词的解释要复杂一些。例如，当子类型被解释为等式时，约束生成规则可以这样理解：对于（$\mathrm{t}: \forall \overline{\mathrm{X}} . \mathrm{T}$）的有效类型形式是$\mathrm{T}$，对于类型变量$\overline{\mathrm{X}}$的某些选择，前提是对于所有$\overline{\mathrm{X}}$的选择，$\mathrm{t}$具有类型$\mathrm{T}$。

我们注意到（$t: \forall \overline{\mathrm{X}} . \mathrm{T}$）必须是一种新的表达式形式：它不能通过向演算中添加新常量来编码——而（$t: \exists \bar{X} . T$）却可以，因为现有的约束生成规则都不会产生普遍量化约束。与所有类型注释一样，它具有标识语义。

通用类型注释与存在类型注释的比较有什么用？当类型变量存在性地绑定时，类型检查器可以自由地给它分配任何使程序类型正确的值。因此，表达式 $(\lambda z . z + 1: \exists X . X \rightarrow X)$ 和 $(\lambda z . z: \exists X . X \rightarrow X)$ 都是类型正确的：在前者情况下，$X$ 被分配为 int，而在后者中则保持未确定。然而，有时坚持表达式应该是多态的很有用。这种效果可以通过使用普遍绑定的类型变量自然地实现。实际上，$(\lambda z . z + 1: \forall X . X \rightarrow X)$ 是类型错误的，因为 $\forall X .(X=$ int) 是假的，而 $(\lambda z . z: \forall X . X \rightarrow X)$ 是类型正确的。

1.10.5 练习 $[\star]$ ：写下约束 $\exists z \cdot \llbracket(\lambda z \cdot z \hat{+} \hat{1}: \forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}): \mathrm{Z} \rrbracket$ 和 $\exists Z . \llbracket(\lambda z . z: \forall X . X \rightarrow X): z \rrbracket$，这些约束指明了这些表达式是否类型正确。检查前者是错误的，而后者是可以满足的。

一个通用的类型注释，如上所述，不过是（封闭的）Damas-Milner类型方案。因此，新的构造（$t: \forall \overline{\mathrm{X}} . \mathrm{T}$）使我们能够确保表达式$t$承认类型方案$\forall \overline{\mathrm{X}}.T$。这一特性在ML编程语言的模块级别中被利用，在那里需要检查推断的模块组件$t$的类型比模块签名中出现的类型方案$\mathrm{S}$更为通用。在我们看来，这个过程简单来说就是确保$(t: S)$类型正确。

在第1.9节中，我们指出局部的（即闭合的）类型注解表达能力有限，因为它们不能共享类型变量。为了克服这个限制，我们引入了表达式形式 $\exists \overline{\mathrm{X}}$. $\mathrm{t}$ 和 ( $\mathrm{t}: \mathrm{T}$ )。前者在 $t$ 中绑定类型变量 $\overline{\mathrm{X}}$，使它们能在类型注解中使用，并指示约束生成器在这个点存在性地量化它们。后者要求 $t$ 具有 $T$。在普遍类型注解的情况下，以同样的方式继续是自然的。我们现在引入表达式形式 $\forall \overline{\mathrm{X}}$.t，它同样在 $t$ 中绑定 $\overline{\mathrm{X}}$，但带有不同的约束生成规则：

$$
\llbracket \forall \overline{\mathrm{x}} . \mathrm{t}: \mathrm{T} \rrbracket=\forall \overline{\mathrm{X}} \cdot \exists \mathrm{Z} \cdot \llbracket \mathrm{t}: \mathrm{Z} \rrbracket \wedge \exists \overline{\mathrm{X}} \cdot \llbracket \mathrm{t}: \mathrm{T} \rrbracket \quad \text { provided } \overline{\mathrm{X}} \# f t v(\mathrm{~T}) \wedge \mathrm{Z} \notin f t v(\mathrm{t})
$$

这条规则比与表达式形式 $\exists \bar{X}$.t 关联的规则要复杂一些。这同样是因为我们不想过度限制 T。下面第一个练习展示了更为天真的版本的规则并不能产生预期的效果。第二个练习显示了这一版本可以。第三个练习则澄清了一个效率问题。

1.10.6 练习 $[\star]$ ：假设 $\llbracket \forall \overline{\mathrm{X}} . \mathrm{t}: \mathrm{T} \rrbracket$ 定义为 $\forall \overline{\mathrm{X}}$. $\llbracket \mathrm{t}: \mathrm{T} \rrbracket$，条件是 $\overline{\mathrm{X}} \# \operatorname{ftv}(\mathrm{T})$。写下约束 $\llbracket \forall \mathrm{X} .(\lambda \mathrm{z} \cdot \mathrm{z}: \mathrm{X} \rightarrow \mathrm{X}): \mathrm{Z} \rrbracket$。你能描述它的解吗？它有预期的含义吗？

1.10.7练习 $[\star \star]$ ：设 $\overline{\mathrm{x}} \supseteq f t v(\mathrm{~T})$ 且 $\overline{\mathrm{x}} \# f t v(\mathrm{t})$ 。检查约束 $\llbracket(\mathrm{t}: \forall \overline{\mathrm{X}} . \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ 和 $\llbracket \forall \overline{\mathrm{X}} .(\mathrm{t}: \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ 是否等价。换句话说，局部通用类型注解也可以用上述更复杂结构来表达。

1.10.8 练习 $[\star \star \star \star, \nrightarrow]$ ：上述出现的约束生成规则损害了约束生成的线性时间和空间复杂度，因为它复制了项 $t$。有可能避免这个问题，但这需要对约束语言进行轻微的泛化。让我们在 $C_{2}$ 中写下 $\mathrm{x}:\forall \underline{\underline{X}} \bar{Y}[C_{1}].\mathrm{T}$ 用于 $\forall \overline{\mathrm{X}}.\exists \overline{\mathrm{Y}}.C_{1} \wedge$ 定义 $\mathrm{x}:\forall \overline{\mathrm{X}} \overline{\mathrm{Y}}[C_{1}].\mathrm{T}$ 在 $C_{2}$ 中。在这种扩展的 let 形式中，下划线的变量 $\overline{\mathrm{x}}$ 被解释为刚性的，而不是灵活的，同时在检查 $C_{1}$ 是否可满足时。然而，与 $\mathrm{x}$ 相关联的类型方案不受影响。检查上述约束生成规则现在可以按照以下方式编写：

$$
\llbracket \forall \overline{\mathrm{X}} . \mathrm{t}: \mathrm{T} \rrbracket=\text { let } \mathrm{x}: \forall \underline{\mathrm{x}} \mathrm{z}[\llbracket \mathrm{t}: \mathrm{Z} \rrbracket] . \mathrm{Z} \text { in } \mathrm{x} \preceq \mathrm{T} \quad \text { provided } \mathrm{Z} \notin f t v(\mathrm{t})
$$

大致来说，新规则为$t$形成了一种最一般的类型模式，确保类型变量$\overline{\mathrm{X}}$在其中不受限制，并检查$\mathrm{T}$是其一个实例。此外，它不会重复t。为了完成这个练习，扩展约束求解器的规格说明（图1-12和116），以及它的实现，以处理这种约束语言的扩展。

总之，让我们再次强调，如果$\mathrm{T}$具有自由类型变量，类型注释（$\mathrm{t}: \mathrm{T}$）的效果取决于它们是如何和在哪里绑定的。如何绑定的效果源于这样一个事实：普遍绑定类型变量而非存在性绑定会导致更严格的约束。实际上，我们让读者验证$\llbracket \forall \overline{\mathrm{X}} . \mathrm{t}: \mathrm{T} \rrbracket$蕴含$\llbracket \exists \overline{\mathrm{X}} . \mathrm{t}: \mathrm{T} \rrbracket$，而反之则通常不成立。在哪里绑定的效果，在存在性绑定类型变量的情况下，已在第1.9节中说明。这种情况下的原因在于let和$\exists$不交换。在普遍绑定类型变量情况下，可能归因于$\forall$和$\exists$不交换的事实。例如，$\lambda \mathrm{z} . \forall \mathrm{X} .(\mathrm{z}: \mathrm{x})$是类型错误的，因为在$\lambda$抽象内部，不能说程序变量$\mathrm{z}$具有每种类型。然而，$\forall \mathrm{X} . \lambda \mathrm{z} .(\mathrm{z}: \mathrm{X})$是类型正确的，因为身份函数确实对每个$\mathrm{X}$都有类型$\mathrm{X} \rightarrow \mathrm{X}$。

1.10.9 练习 $[\star]$：写下约束 $\exists Z . \llbracket \lambda z . \forall x .(z: x): z \rrbracket$ 和 $\exists Z . \llbracket \forall x . \lambda z .(z: X): Z \rrbracket$，这些约束说明这些表达式是否类型正确。前者是否可满足？后者呢？

在标准ML和Objective Caml中，类型注释中出现的类型变量是隐式绑定的。也就是说，语言中没有用于构造 $\exists \bar{X}$ 和 $\forall \bar{x}$.t 的语法。当一个类型注释（ $t: T$ ）包含一个自由类型变量 $\mathrm{X}$ 时，一个固定的约定决定了如何以及在哪里绑定 $\mathrm{X}$ 。在标准ML中， $\mathrm{X}$ 在最近的 val 绑定中普遍绑定，这个绑定包含了所有相关的 $\mathrm{X}$ 出现（Milner, Tofte, 和 Harper, 1990）。1997年对标准ML的修订（Milner, Tofte, Harper, 和 MacQueen, 1997b）通过允许在 val 绑定中显式引入类型变量，略微改进了这种情况。然而，它们仍然必须是普遍绑定的。在Objective Caml中， $\mathrm{X}$ 在最近的顶层 let 绑定中存在性地绑定；这种行为似乎目前没有文档记录。我们认为，（i）允许隐式引入类型变量是令人困惑的；以及（ii）为了表达性，应该向程序员提供普遍和存在量词。令人惊讶的是，尽管这些问题很可能已经很长时间被视为“民间传统”，但关于这些语言设计和类型推断的问题在文献中似乎鲜少受到关注。Peyton Jones 和 Shields (2003) 在 Haskell 的背景下研究这些问题，并同意（i）。关于（ii），他们似乎认为语言设计者必须在存在和普遍类型变量引入形式之间进行选择——他们将这两种形式称为“类型共享”和“类型lambda”，而我们指出它们可以也应该共存。

多态递归

例子1.2.10解释了如何在ML编程语言中看待letrec构造，它可以被视为常量fix的一个应用，包装在普通的let构造内部。练习1.9.6表明这产生了一个有些限制性的约束生成规则：泛化仅在fix应用类型检查之后发生。换句话说，在letrec $f=\lambda$ z.t $_{1}$ in $t_{2}$中，$t_{1}$中所有$f$的出现必须具有相同的（单态）类型。这种限制有时很麻烦，似乎没有根据：如果正在定义的函数是多态的，那么即使在其自己的定义内部，也应该能够使用不同的类型。实际上，Mycroft（1984）扩展了Damas和Milner的类型系统，加入了对递归更宽松的处理，通常称为多态递归。这个想法是只要求$t_{1}$中$f$的出现具有相同的类型方案。因此，它们可能有不同的类型，但都是共同类型方案实例。后来证明，在Mycroft扩展的类型系统中，类型良好性是不可判定的（Henglein, 1993; Kfoury, Tiuryn, 和 Urzyczyn, 1993）。为了绕过这个难题，一个解决方案是使用半算法，如果它在合理的时间内不成功或失败，则退回到单态递归。尽管这样的解决方案在自动化程序分析的背景下可能很有吸引力，但在程序员可见的类型系统背景下则不太吸引人，因为它可能变得难以理解为什么程序是类型不良的。因此，我们描述了一个更简单的解决方案，即要求程序员显式地为f提供一个类型方案。这是强制类型注释的一个实例。

首先，我们必须改变fix的状态，因为如果fix保持不变，那么$f$必须保持$\lambda$-绑定，并且不能接受多态类型方案。我们将fix转换成一种语言构造，它绑定一个程序变量$f$，并用DM类型方案对其进行注释。因此，值和表达式的语法扩展如下：

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-113.jpg?height=56&width=801&top_left_y=1202&top_left_x=742)

请注意，$f$ 在 $\lambda$ 中绑定，使得操作语义如下扩展。

$$
\begin{equation*}
(f i x f: S . \lambda z . t) v \longrightarrow(\text { let } f=f i x f: S . \lambda z . t \text { in } \lambda z . t) v \tag{R-FIX'}
\end{equation*}
$$

类型注释 $\mathrm{S}$ 在归约中不起重要作用；它只是被保留下来。现在可以定义 letrec $\mathrm{f}: \mathrm{S}=\lambda \mathrm{z}_{\mathrm{t}} \mathrm{t}_{1}$ 在 $\mathrm{t}_{2}$ 中作为语法糖，等同于 let $f=f i x f: S . \lambda z . t_{1}$ 在 $t_{2}$ 中。

我们现在给出一个用于fix的约束生成规则：

$$
\llbracket f i x f: S . \lambda z . t: T \rrbracket=\text { let } f: S \text { in } \llbracket \lambda z . t: S \rrbracket \wedge S \preceq T
$$

左边的连接词要求函数 $\lambda z$.t 具有类型方案 $S$，在假设 $f$ 具有类型 $S$ 的条件下。因此，现在在 $t$ 中的不同出现的 $f$ 可以接收不同的类型。如果 $S$ 是 $\forall \bar{X}$. $T$，其中 $\overline{\mathrm{X}} \# \mathrm{ftv}(\mathrm{t})$，那么我们用 $\llbracket t: S \rrbracket$ 表示 $\forall \bar{X}$. $\llbracket t: T \rrbracket$。实际上，检查多态类型注释的有效性—无论是强制的，正如这里的情况，还是可选的，像之前的情况—需要一个普遍量化的约束。右边的连接词仅仅限制 $\mathrm{T}$ 为 $\mathrm{S}$ 的一个实例。

给定letrec的定义 $f: S=\lambda z \cdot t_{1}$ 在 $t_{2}$ 中作为语法糖，上述规则导致了以下对letrec的派生约束生成规则：

[ 让递归 $f: S=\lambda$ z.t $t_{1}$ 在 $t_{2}: T$ 的意思是：让 $f: S$ 在 $(\llbracket \lambda z . t_{1}: S \rrbracket \wedge \llbracket t_{2}: T \rrbracket)$ ]

这条规则可以说是相当自然的。程序变量$f$在其作用域内被赋予类型方案$S$，即无论是在函数定义内部还是外部。函数$\lambda$ z.t $_{1}$本身必须具有类型方案$\mathrm{S}$。最后，$\mathrm{t}_{2}$必须具有类型$\mathrm{T}$，正如每个let构造中那样。

1.10.10 练习 $[\star \star]$ ：证明上述导出的约束生成规则确实是有效的。

证明扩展语言仍然具有主题减少是直接的。这个证明依赖于以下引理：如果 $t$ 具有类型方案 $S$，那么 $S$ 的每个实例也都是 $t$ 的有效类型。

1.10.11 引理：若 $\llbracket \mathrm{t}: \mathrm{S} \rrbracket \wedge \mathrm{S} \preceq \mathrm{T}$，则 $\Vdash \llbracket \mathrm{t}: \mathrm{T} \rrbracket$.

1.10.12 定理 [主题约简]：(R-Fix') ⊆(≤)。

Haskell编程语言（Hudak, Peyton Jones, Wadler, Boutel, Fairbairn, Fasel, Guzman, Hammond, Hughes, Johnsson, Kieburtz, Nikhil, Partain, 和 Peterson, 1992）提供了多态递归。关于其类型规则的有趣细节可以在（Jones, 1999）中找到。

值得指出的是，在某些多态递归情况下，某些受限的类型推断是可决定的。这通常在某些程序分析中是如此，其中程序的类型推导已经可用，目标仅仅是推断额外的原子注释，例如绑定时间或严格性属性。利用这一想法的几篇论文包括（Dussart, Henglein, 和 Mossin, 1995a; Jensen, 1998; Rehof 和 Fähndrich, 2001）。

## Universal types

ML类型系统在类型和类型方案之间实施严格的分层，换句话说，它只允许在类型内部使用前缀全称量化器。我们之前已经指出这样做是有充分理由的：ML类型系统的类型推断是可判定的，而没有任何此类限制的System F的类型推断是不可判定的。然而，这种限制在表达能力上是有代价的：它阻止了高阶函数接受多态函数参数，并禁止将多态函数存储在数据结构中。幸运的是，实际上可以通过要求程序员提供额外的类型信息来绕过这个问题。

我们即将描述的方法让人联想到代数数据类型定义允许绕过与等递归类型相关的问题（第1.9节）。因为我们不希望用形式为 $\forall \bar{Y}$.T的全局类型来扩展类型的语法，所以我们允许使用以下形式的普遍类型定义：

$$
\mathrm{D} \overrightarrow{\mathrm{X}} \approx \forall \overline{\mathrm{Y}} . \mathrm{T}
$$

其中D仍然表示数据类型。如果D具有签名$\vec{\kappa} \Rightarrow \star$，那么类型变量$\overrightarrow{\mathrm{X}}$必须有种类$\vec{\kappa}$。类型$\mathrm{T}$必须有种类$\star$。类型变量$\overline{\mathrm{X}}$和$\overline{\mathrm{Y}}$被认为在$\mathrm{T}$内是绑定的，并且定义必须是闭合的，即$f t v(\mathrm{~T}) \subseteq \overline{\mathrm{X}} \overline{\mathrm{Y}}$必须成立。最后，类型构造器D的变异性必须与其定义相匹配——这一要求表述如下：

1.10.13 定义：设 $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \forall \overline{\mathrm{Y}}$。$\mathrm{T}$ 和 $\mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \approx \forall \overline{\mathrm{Y}}^{\prime} \cdot \mathrm{T}^{\prime}$ 是同一普遍类型定义的两个 $\alpha$-等价实例，使得 $\overline{\mathrm{Y}} \# \operatorname{ftv}\left(\mathrm{T}^{\prime}\right)$ 和 $\overline{\mathrm{Y}}^{\prime} \# \operatorname{ftv}(\mathrm{T})$。那么，$\mathrm{D} \overrightarrow{\mathrm{X}} \leq \mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \Vdash \forall \overline{\mathrm{Y}}^{\prime} . \exists \overline{\mathrm{Y}} . \mathrm{T} \leq \mathrm{T}^{\prime}$ 必须成立。

这个要求与定义1.9.8中找到的要求相似。其理念是，如果$D \vec{X}$和$D \vec{X}^{\prime}$可以比较，那么它们的展开$\forall \bar{Y}$. $T$和$\forall \bar{Y}^{\prime} \cdot T^{\prime}$也应该可以比较。它们之间的比较通过约束$\forall \overline{\mathrm{Y}}^{\prime} . \exists \overline{\mathrm{Y}} . \mathrm{T} \leq \mathrm{T}^{\prime}$表达，其含义可能是：每个$\forall \overline{\mathrm{Y}}^{\prime} . \mathrm{T}^{\prime}$的实例（是一种超类型）都是$\forall \bar{Y}$.T的一个实例。同样，当子类型被解释为等价时，定义1.10.13的要求总是得到满足；只有当真正存在子类型时，它才变得非平凡。

通用类型定义 $D \vec{X} \approx \forall \bar{Y} . T$ 的效果是为编程语言增加了一个新的构造：

$$
\mathrm{v}::=\ldots \mid \text { pack }_{\mathrm{D}} \mathrm{v} \quad \mathrm{t}::=\ldots \mid \text { pack }_{\mathrm{D}} \mathrm{t} \quad \mathcal{E}::=\ldots \mid \text { pack }_{\mathrm{D}} \mathcal{E}
$$

以及一个新的一元析构函数开放 $\mathrm{D}_{\mathrm{D}}$。它们的操作语义如下：

$$
\begin{equation*}
\text { open }_{\mathrm{D}}\left(\operatorname{pack}_{\mathrm{D}} \mathrm{v}\right) \xrightarrow{\delta} \mathrm{v} \tag{R-OPEN-ALL}
\end{equation*}
$$

直观地说，$\operatorname{pack}_{D}$ 和 $\operatorname{open}_{D}$ 是证明 $\mathrm{D} \overrightarrow{\mathrm{X}}$ 与 $\forall \overline{\mathrm{Y}}$.T. 之间同构的两个强制转换。值 $\mathrm{pack}_{\mathrm{D}} \mathrm{v}$ 的行为与 $\mathrm{v}$ 完全一样，除了它被标记了，这是给类型检查器的一个提示。因此，在使用该值之前，必须使用 $\mathrm{open}_{\mathrm{D}}$ 移除这个标记。

pack $_{D}$ 和 open ${ }_{D}$ 的打字规则是什么？在系统F中，它们的类型分别是 $\forall \overline{\mathrm{X}} .(\forall \overline{\mathrm{Y}} . \mathrm{T}) \rightarrow \mathrm{D} \overrightarrow{\mathrm{X}}$ 和 $\forall \overline{\mathrm{X}}$.D $\overrightarrow{\mathrm{X}} \rightarrow \forall \overline{\mathrm{Y}}$.T。然而，这两个都不是有效的类型方案：它们都在箭头下展示了全称量化符。

在 $\mathrm{pack}_{\mathrm{D}}$ 的例子中，它已经被制成一个语言构造而不是一个常量，我们通过将这个普遍量词嵌入到约束生成规则中来绕过这个问题：

$$
\llbracket \text { pack }_{\mathrm{D}} \mathrm{t}: \mathrm{T}^{\prime} \rrbracket=\exists \overline{\mathrm{X}} \cdot\left(\llbracket \mathrm{t}: \forall \overline{\mathrm{Y}} \cdot \mathrm{T} \rrbracket \wedge \mathrm{D} \overrightarrow{\mathrm{X}} \leq \mathrm{T}^{\prime}\right)
$$

该规则隐式要求 $\overline{\mathrm{X}}$ 对左侧必须是新鲜的，且要求 $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \forall \overline{\mathrm{Y}}$。$\mathrm{T}$ 是（$\alpha$-变体）$\mathrm{D}$ 的定义。左侧连接要求 $t$ 具有类型方案 $\forall \bar{Y}$.T。符号 $\llbracket t ~: ~ S \rrbracket$ 在第114页定义。右侧连接说明 $\mathrm{pack}_{\mathrm{D}} \mathrm{t}$ 的有效类型是（D $\overrightarrow{\mathrm{X}}$ 的）超类型。

我们以下面这种方式处理开放。假设 $\overline{\mathrm{X}} \# \overline{\mathrm{Y}}$，我们将初始环境 $\Gamma_{0}$ 扩展为带绑定开放的 $\mathrm{D}_{\mathrm{D}}: \forall \overline{\mathrm{X}} \mathrm{Y} . \mathrm{D} \overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}$。我们只是将全称量化符提到了箭头外面——在System F中这是一种有效的同构。

主题还原定理的证明必须扩展以下新情况：

1.10.14 定理 [主体还原]：(R-OPEn-AlL) ⊆(≤)。

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

其中（1）是根据应用和常量的约束生成定义；Z是新的；（2）是根据 pack $_{\mathrm{D}}$ 和 open ${ }_{\mathrm{D}}$ 的约束生成定义，其中 $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \forall \overline{\mathrm{Y}}$。$\mathrm{T}$ 和 $\mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \approx \forall \overline{\mathrm{Y}}^{\prime} . \mathrm{T}^{\prime}$ 是定义 $\mathrm{D}$ 的两个 $\alpha$-等价实例；$\overline{\mathrm{X}}, \overline{\mathrm{Y}}, \overline{\mathrm{X}}^{\prime}$ 和 $\overline{\mathrm{Y}}^{\prime}$ 都是新的，并且满足 $\overline{\mathrm{Y}} \# \mathrm{ftv}\left(\mathrm{T}^{\prime}\right)$ 和 $\overline{\mathrm{Y}}^{\prime} \# \operatorname{ftv}(\mathrm{T})；（3）$ 是根据 C-ExAnd、C-Arrow 和 C-ExTrans，这允许消除 Z；（4）是根据定义 1.10.13、引理 1.10.1 和 C-ExAnd；（5）是根据引理 1.10 .11 和 1.6 .3；（6）是根据 C-Ex*。

证明 $(\mathrm{R}-$ 上下文 $) \subseteq(\sqsubseteq)$ 也必须用一个新的子案例来扩展，对应于新的产生式 $\mathcal{E}::=\ldots \mid \operatorname{pack}_{\mathrm{D}} \mathcal{E}$。如果语言是纯的，这很简单。然而，在存在副作用的情况下，这个子案例是失败的，因为约束中的全称和存在量词不交换。然后通过将 pack $_{\mathrm{D}}$ 限制在值上，如定义 1.7.7 中所述，来避免这个问题。

这种将ML类型系统扩展为带有普遍类型（或存在类型 - 见下文）的方法已经在（Läufer和Odersky，1994年）中研究过；

Rémy, 1994; Odersky和Läufer, 1996; Shields和Peyton Jones, 2002)。Läufer和Odersky建议将通用或存在类型声明与代数数据类型定义相结合。这允许抑制繁琐的pack $\mathrm{D}_{\mathrm{D}}$ 和 open $\mathrm{D}_{\mathrm{D}}$ 结构；相反，只需使用构造和分解变体和记录的标准语法即可。

## 存在类型

存在类型（TAPL第24章）是与普遍类型紧密相关的，可以以同样的方式引入ML类型系统。实际上，存在类型在ML类型系统中早在普遍类型之前就已经被引入了。我们简要描述了这一扩展，主要强调与普遍类型情况的区别。

我们现在允许存在类型定义，形式为 $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \exists \overline{\mathrm{Y}}$.T。对于一个良好形成的定义所需的条件没有改变，除了变异性要求，它是双重的：

1.10.15 定义：设 $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \exists \overline{\mathrm{Y}}$。$\mathrm{T}$ 和 $\mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \approx \exists \overline{\mathrm{Y}}^{\prime} \cdot \mathrm{T}^{\prime}$ 是同一存在类型定义的两个 $\alpha$-等价实例，使得 $\overline{\mathrm{Y}} \# \operatorname{ftv}\left(\mathrm{T}^{\prime}\right)$ 和 $\overline{\mathrm{Y}}^{\prime} \# \operatorname{ftv}(\mathrm{T})$。那么，$\mathrm{D} \overrightarrow{\mathrm{X}} \leq \mathrm{D} \overrightarrow{\mathrm{X}}^{\prime} \Vdash \forall \overline{\mathrm{Y}} \cdot \exists \overline{\mathrm{Y}}^{\prime} . \mathrm{T} \leq \mathrm{T}^{\prime}$ 必须成立。

这种存在类型定义的效果是为编程语言增加一个新的一元构造器 pack $_{\mathrm{D}}$ 以及一个新的构造：$t::=\ldots \mid$ open $_{\mathrm{D}} \mathrm{t} t$ 和 $\mathcal{E}::=\ldots\left|\operatorname{open}_{\mathrm{D}} \mathcal{E} \mathrm{t}\right| \operatorname{open}_{\mathrm{D}} \mathrm{v} \mathcal{E}$. 它们的操作语义如下：

$$
\begin{equation*}
\text { open }_{\mathrm{D}}\left(\text { pack }_{\mathrm{D}} \mathrm{v}_{1}\right) \mathrm{v}_{2} \longrightarrow \mathrm{v}_{2} \mathrm{v}_{1} \tag{R-OPEN-Ex}
\end{equation*}
$$

在文献中，open $\mathrm{D}_{\mathrm{D}}$ 的第二个参数通常需要是一个 $\lambda$-抽象 $\lambda$ z.t，因此构造变为 open $_{D} t(\lambda z . t)$，常写作 open $_{D} t$ 作为 $z$ 在 $t$ 中。

提供了 $\overline{\mathrm{X}} \# \overline{\mathrm{Y}}$，我们将初始环境 $\Gamma_{0}$ 扩展为绑定包 $_{D}: \forall \bar{X} \bar{Y} . T \rightarrow D \vec{X}$。开放 ${ }_{D}$ 的约束生成规则如下：

$$
\llbracket \text { open }_{\mathrm{D}} \mathrm{t}_{1} \mathrm{t}_{2}: \mathrm{T}^{\prime} \rrbracket=\exists \overline{\mathrm{X}} .\left(\llbracket \mathrm{t}_{1}: \mathrm{D} \overrightarrow{\mathrm{X}} \rrbracket \wedge \llbracket \mathrm{t}_{2}: \forall \overline{\mathrm{Y}} . \mathrm{T} \rightarrow \mathrm{T}^{\prime} \rrbracket\right)
$$

该规则隐式要求 $\overline{\mathrm{X}}$ 对左侧是新鲜的，$\overline{\mathrm{Y}}$ 对 $\mathrm{T}^{\prime}$ 是新鲜的，且 $\mathrm{D} \overrightarrow{\mathrm{X}} \approx \forall \overline{\mathrm{Y}} . \mathrm{T}$ 是（一个 $\alpha$-变体）$\mathrm{D}$ 的定义。左侧连词简单要求 $t_{1}$ 具有类型 $D \vec{X}$。右侧连词指出函数 $t_{2}$ 必须准备好接受任何 $\overline{\mathrm{Y}}$ 的类型 $\mathrm{T}$ 的参数，并产生预期类型 $\mathrm{T}^{\prime}$ 的结果。换句话说，$t_{2}$ 必须是一个多态函数。

存在包 ${ }_{D}$ 的类型方案与普遍开 $\mathrm{D}_{D}$ 类似，而存在笔 $_{D}$ 的约束生成规则与普遍包 $\mathrm{D}_{\mathrm{D}}$ 的规则是近亲。因此，普遍类型与存在类型之间的对偶性相当强。主要区别在于，存在开 $\mathrm{D}_{\mathrm{D}}$ 结构是二元的，而不是一元的，以限制新引入的类型变量 $\bar{Y}$ 的作用域。通过研究以普遍类型表示存在类型的方式（Reynolds, 1983b），可以更好地理解这种对偶性。

如预期的那样，R-OPEn-Ex 保留了类型。

1.10.16 定理 [主体还原]：(R-OpEn-Ex) ⊆(≤)。

1.10.17 练习 $[\star \star, \nrightarrow]$ ：证明定理1.10.16。这个证明与定理1.10.14的证明相似，尽管不是完全相同。

在存在副作用的情况下，新的生产$\mathcal{E}::=\ldots \mid$ open $_{D}$ v $\mathcal{E}$是有问题的。标准的解决方法是限制open $_{D}$的第二个参数必须是一个值。

### 1.11 Rows

在1.9节中，我们已经展示了如何用代数数据类型扩展ML编程语言，也就是变体和记录类型定义，我们现在称之为简单。这种机制有一个严重的限制：两个不同的定义必须定义不兼容的类型。因此，人们无法希望编写能够统一操作不同形状的变体或记录的代码，因为这类代码的类型甚至无法表达。

例如，无法表达多态记录访问操作的类型，这种操作检索存储在记录内特定字段ℓ处的值，而不管记录中是否存在其他字段。实际上，如果标签ℓ在简单记录类型$D \vec{X}$的定义中以类型$T$出现，则相关的记录访问操作具有类型$\forall \overline{\mathrm{X}}.D \overrightarrow{\mathrm{X}} \rightarrow \mathrm{T}$。如果ℓ在另一个简单记录类型，比如说$\mathrm{D}^{\prime} \overrightarrow{\mathrm{X}}^{\prime}$的定义中以类型$\mathrm{T}^{\prime}$出现，则相关的记录访问操作具有类型$\forall \overline{\mathrm{X}}^{\prime} . \mathrm{D}^{\prime} \overrightarrow{\mathrm{X}}^{\prime} \rightarrow \mathrm{T}^{\prime}$；依此类推。涵盖所有这些不可比较类型方案的最精确类型方案是$\forall \mathrm{XY} . \mathrm{X} \rightarrow \mathrm{Y}$。然而，这并不是记录访问操作的合适类型方案。另一种目前无法表达类型的强大操作是多态记录扩展，它复制一个记录并在副本中存储字段ℓ的值，如果之前不存在该字段，可能会创建该字段，同样不管记录中是否存在其他字段。（如果已知ℓ之前存在，该操作被称为多态记录更新。）

为了给多态记录操作分配类型，我们必须摒弃记录类型定义：我们必须用提供记录领域和内容的直接描述的结构化记录类型替换命名的记录类型，比如 D $\overrightarrow{\mathrm{X}}$。 （鉴于记录与从标签到值的部分函数之间的类比，我们使用“领域”一词来指代在记录中定义的字段集合。）例如，乘积类型是结构化的：类型$T_{1} \times T_{2}$是未声明类型的对，其第一个组成部分具有类型$\mathrm{T}_{1}$，第二个组成部分具有类型$\mathrm{T}_{2}$。因此，我们希望设计出与乘积类型非常相似的记录类型。在这样做时，我们面临两个正交的困难。首先，与对相比，记录可能具有不同的领域。因为类型系统必须静态确保不会访问未定义的字段，所以关于记录领域的 信息必须成为其类型的一部分。其次，由于我们取消了记录类型定义，标签现在必须预定义。然而，出于效率和模块化的原因，不可能在每一个记录类型中显式列出所有存在的标签。

在以下内容中，我们解释了如何在简单的有限标签集合设置中解决第一个难题。然后，我们引入了行（rows），这允许处理无限标签集合，并解决第二个难题。我们定义了行的语法和逻辑解释，研究在它们出现时产生的新约束等价定律，并扩展了支持行的第一阶统一算法。接着，我们回顾了行的几个应用，包括对记录、变体和对象的多态操作，并讨论了行的替代方案。

具有有限承运人的记录##

让我们暂时假设 $\mathcal{L}$ 是有限的。实际上，为了明确起见，让我们假设 $\mathcal{L}$ 是 $\left\{\ell_{a}, \ell_{b}, \ell_{c}\right\}$。

首先，让我们只考虑完整的记录，其域恰好是$\mathcal{L}$——换句话说，由$\mathcal{L}$索引的元组。为了描述它们，很自然地引入一个类型构造器record，其签名是$\star \otimes \star \otimes \star \Rightarrow \star$。类型记录$\mathrm{T}_{a} \mathrm{~T}_{b} \mathrm{~T}_{c}$表示所有这样的记录：其中字段$\ell_{a}$（分别是$\ell_{b}, \ell_{c}$）包含类型为$\mathrm{T}_{a}$（分别是$\mathrm{T}_{b}, \mathrm{~T}_{c}$）的值。请注意，record不过是 arity 3 的乘积类型构造器。对记录的基本操作，即基于默认值创建记录，该默认值存储在每个字段中，更新特定字段（例如$\ell_{b}$），以及访问特定字段（例如$\ell_{b}$），可以分配以下类型方案：

$$
\begin{aligned}
\{\cdot\}: & \forall \mathrm{X} . \mathrm{X} \rightarrow \text { record } \mathrm{X} \mathrm{X} \mathrm{X} \\
\left\{\cdot \text { with } \ell_{b}=\cdot\right\}: & \forall \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{b}^{\prime} \mathrm{X}_{c} \cdot \text { record } \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{c} \rightarrow \mathrm{X}_{b}^{\prime} \rightarrow \text { record } \mathrm{X}_{a} \mathrm{X}_{b}^{\prime} \mathrm{X}_{c} \\
\cdot\left\{\ell_{b}\right\}: & \forall \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{c} \cdot \text { record } \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{c} \rightarrow \mathrm{X}_{b}
\end{aligned}
$$

在这里，多态性允许在不了解其他字段类型的情况下更新或访问字段。这种灵活性是由所有记录类型都是使用单个记录类型构造函数形成的属性所实现的。

这很正确，但一般来说，记录的域不一定是 $\mathcal{L}$ ：它可能是 $\mathcal{L}$ 的一个子集。在保持上述关键属性的同时，我们如何处理这个事实？一种朴素的方法是使用标准代数数据类型选项来编码任意记录，其定义为选项 $\mathrm{X} \approx$ pre $\mathrm{X}+$ abs。我们用 pre 表示存在，用 abs 表示缺失：实际上，定义为值 $\mathrm{v}$ 的字段被编码为带有值 pre $\mathrm{v}$ 的字段，而未定义的字段则被编码为带有值 abs 的字段。因此，如果一个任意记录的字段如果存在，分别具有类型 $\mathrm{T}_{a}, \mathrm{~T}_{b}$ 和 $\mathrm{T}_{c}$，则可以编码为类型为 record (option $\mathrm{T}_{a}$ ) (option $\mathrm{T}_{b}$ ) (option $\mathrm{T}_{c}$ ) 的完整记录。这种朴素方法有一个严重的缺点：记录类型仍然不包含域信息。因此，字段访问必须涉及动态检查，以确定所需的字段是否存在：在我们的编码中，这对应于使用 case 选项。

为了避免这种开销并提高编程安全性，我们必须将这种检查从运行时移动到编译时。换句话说，我们必须让类型系统意识到pre和abs之间的区别。为此，我们用两个独立的代数数据类型定义替换了option的定义，分别是pre X ≈ pre X 和 abs ≈ abs。换句话说，我们引入了一个一元类型构造器pre，它唯一关联的数据构造器是pre，以及一个零元类型构造器abs，它唯一关联的数据构造器是abs。记录类型现在包含了域信息：例如，类型为record abs (pre Tb) (pre Tc)的记录必须有域{lb, lc}。因此，字段的类型表明它是否被定义。由于pre类型除了pre没有其他数据构造器，访问器pre^-1，其类型为∀X.pre X → X，允许检索字段中存储的值，不会失败。因此，动态检查已被消除。

为了完成我们编码的定义，我们现在用全记录的操作来定义任意记录的操作。为了区分这两者，我们用尖括号而不是花括号来书写前者。空记录 \langle\rangle ，其中所有字段未定义，可以定义为 $\{ \text{abs} \}$ 。在特定字段（比如说， $\ell_{b}$ ）的扩展 $\left\langle\cdot\right.$ 用 $\left.\ell_{b}=\cdot\right\rangle$ 定义为 $\lambda r . \lambda z .\left\{r\right.$ with $\ell_{b}=$ pre $\left.z\right\}$ 。在特定字段（比如说， $\left.\ell_{b}\right) \cdot\left\langle\ell_{b}\right\rangle$ 的访问定义为 $\lambda$ z.pre ${ }^{-1} z .\left\{\ell_{b}\right\}$ 。很容易验证这些操作具有以下主要类型方案：

$$
\begin{aligned}
\langle\rangle: & \text { record abs abs abs } \\
\left\langle\cdot \text { with } \ell_{b}=\cdot\right\rangle: & \forall \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{b}^{\prime} \mathrm{X}_{c} \cdot \text { record } \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{c} \rightarrow \mathrm{X}_{b}^{\prime} \rightarrow \operatorname{record} \mathrm{X}_{a}\left(\text { pre } \mathrm{X}_{b}^{\prime}\right) \mathrm{X}_{c} \\
\cdot\left\langle\ell_{b}\right\rangle: & \forall \mathrm{X}_{a} \mathrm{X}_{b} \mathrm{X}_{c} \text {.record } \mathrm{X}_{a}\left(\text { pre } \mathrm{X}_{b}\right) \mathrm{X}_{c} \rightarrow \mathrm{X}_{b}
\end{aligned}
$$

需要注意的是，与$\ell_{b}$处的扩展和访问相关联的类型方案在$\mathrm{X}_{a}$和$\mathrm{X}_{c}$中是多态的，这意味着这些操作不仅不依赖于类型，而且也不依赖于字段$\ell_{a}$和$\ell_{c}$的存在与否。此外，扩展在$\mathrm{X}_{b}$中是多态的，这意味着它不依赖于其参数中字段$\ell_{b}$的存在与否。其结果类型中的子项pre $\mathrm{X}_{b}^{\prime}$反映了$\ell_{b}$是在扩展记录中定义的事实。相反，访问操作类型中的子项pre $\mathrm{X}_{b}$反映了要求$\ell_{b}$在其参数中定义的要求。

我们对完整记录的任意记录编码是为了教学目的而进行的。实际上，并不需要进行这样的编码：数据构造器pre和abs没有机器表示，编译器可以自由地以高效的方式在内存中布局记录。然而，这种编码很有趣，因为它提供了一种自然的方式来引入类型构造器pre和abs，它们在我们对多态记录操作的处理中扮演着重要角色。

我们注意到，在我们的编码中，类型构造函数record的参数预期要么是类型变量，要么是由pre或abs形成的，反之，类型构造函数pre和abs不打算出现在其他任何地方。可以使用种类（kinds）来强制执行这个不变量。除了$\star$，让我们引入字段类型的种类$\diamond$。然后，让我们采用以下签名：pre: $\star \Rightarrow \diamond$，abs: $\diamond$，以及record: $\diamond \otimes \diamond \otimes \diamond \Rightarrow \star$。

1.11.1 练习 [\star, 推荐, \rightarrow]：检查上述给出的三种类型方案是否具有良好的种类。每个类型变量的种类是什么？

1.11.2 练习 [$\star \star$，推荐，$\nrightarrow$]：我们的记录类型包含关于每个字段的信息，无论它是否被定义：我们在每个字段的类型中使用pre和abs类型构造器来编码定义性信息。也许更自然的方法是引入一个由$\mathcal{L}$的子集索引的记录类型构造器家族，这样具有不同域的记录类型可以使用不同的构造器形成。例如，空记录的类型为\{\}；只定义字段$\ell_{a}$的记录的类型形式为$\left\{\ell_{a}: \mathrm{T}_{a}\right\}$；只定义字段$\ell_{b}$和$\ell_{c}$的记录的类型形式为$\left\{\ell_{b}: \mathrm{T}_{b} ; \ell_{c}: \mathrm{T}_{c}\right\}$；依此类推。假设类型纪律是Damas和Milner的（即，假设一个仅基于等价的语法模型），是否可以为多态记录访问和扩展分配满意的类型方案？如果为记录类型配备非平凡的子类型关系会有帮助吗？

## 无限载体的记录

有限记录从实际和理论角度来看都是不足的。在实际中，标签集合可能会变得非常大，使得每个记录的类型与标签集合本身一样大，即使实际上只有少数几个标签被定义。从原则上讲，标签集合甚至可能是无限的。实际上，在模块化程序中，整个标签集合可能无法提前知道，这在某种意义上等同于与无限标签集合一起工作。因此，记录必须从无限的标签集合中提取——无论它们的域是有限还是无限。然而，我们可以将注意力限制在几乎恒定的记录上，也就是说，只有有限数量的字段不同的记录。有了这个限制，通过为有限数量的字段提供显式定义和所有其他字段的默认值，就可以构建完整的记录（在所有地方定义），就像在有限情况下一样。例如，记录 $\{\{\{$ false $\}$ with $\ell=1\}$ with $\ell^{\prime}=$ true $\}$ 在字段 $\ell^{\prime}$ 上等于 true，在字段 $\ell$ 上等于 1，在任何其他字段上等于 false。

记录类型是从标签到类型的函数，称为行。然而，为了通用性，我们使用一个一元类型构造器，比如 $\Pi$，作为行和记录类型之间的间接层。此外，我们进一步将注意力限制在行几乎是常量的情况下。（这种性质对于记录值成立并不意味着它也适用于记录类型，因为某些记录的默认值可能具有多态类型，人们可能希望每个字段都具有这种多态类型的不同实例。因此这是一个真正的限制，但是一个合理的限制。）因此，行也可以通过为有限数量的字段给出显式类型，以及为所有其他字段给出默认类型来表示。我们用 $\partial \mathrm{T}$ 表示每个字段类型为 $\mathrm{T}$ 的行，以及用 $\left(\ell: \mathrm{T} ; \mathrm{T}^{\prime}\right)$ 表示在字段 $\ell$ 上类型为 $\mathrm{T}$ 而在其他字段上为 $\mathrm{T}^{\prime}$ 的行。形式上，$\partial$ 是一个一元类型构造器，$\ell$ 是一系列二元类型构造器，使用语法糖 $(\ell: \cdot ; \cdot)$ 来书写。例如，$\Pi\left(\ell\right.$ : bool ; $\left(\ell^{\prime}\right.$ : int ; $\partial$ bool $\left.)\right)$ 是一个记录类型，描述了字段 $\ell$ 携带 bool 类型值，字段 $\ell^{\prime}$ 携带 int 类型值，所有其他字段携带 bool 类型值的记录。实际上，这是上面定义的记录的一个有效类型。实际上，类型 $\Pi\left(\ell^{\prime}\right.$ : int ; $(\ell$ :bool ; $\partial$ bool $\left.)\right)$ 也应该是这个记录的有效类型，因为指定字段的顺序不应该重要。我们实际上将这两种类型视为等价的。此外，代表字段 $\ell$ 上为 bool 类型，其他地方为 $\partial$ bool 的行 $(\ell:$ bool ; $\partial$ bool $)$ 必须也等同于 $\partial$ bool，后者代表到处都是 bool 类型。

记录类型也可能包含类型变量。例如，记录 $\lambda z .\{z\}$ 将任何值 $\mathrm{v}$ 映射到一个具有默认值 $\mathrm{v}$ 的记录，其类型为 $\mathrm{X} \rightarrow \Pi(\partial \mathrm{x})$。此记录在任何字段上的投影都将返回相同类型 $\mathrm{X}$ 的值。相比之下，读取其（记录）参数中某个字段 $\ell$ 的函数具有类型 $\Pi(\ell: X ; Y) \rightarrow X$：这意味着参数必须是一个记录，其中字段 $\ell$ 具有类型 $\mathrm{X}$，其他字段可以是任何类型。变量 $\mathrm{Y}$ 被称为行变量，因为它可以实例化为任何行。例如，Y 可以实例化为 $\left(\ell^{\prime}:\right.$ int $\left.; \mathrm{Y}^{\prime}\right)$，结果这个函数可以应用于上面的记录。反之，行 $\partial \mathrm{x}$，等于 $\left(\ell^{\prime}: \mathrm{x} ; \mathrm{x}\right)$，只能实例化为形式 $\partial \mathrm{T}$ 的行，它们等于 $\left(\ell^{\prime}: \mathrm{T} ; \mathrm{T}\right)$，即常量行。

行类型的语法##

令 $\mathcal{L}$ 为一个可数标签的集合。我们用 $\ell . L$ 表示 $\{\ell\} \uplus L$，这意味着 $\ell \notin L$。我们首先引入“种类”，以便将诸如（$\ell$ : int ; $\partial$ bool）这样的行与基本类型，如int或int $\rightarrow$ int区分开来。

1.11.3 定义 [行种类]：行种类由特定的种类类型和由种类 $\operatorname{Row}(L)$ 组成的集合构成，其中 $L$ 在 $\mathcal{L}$ 的有限子集范围内变动。我们使用字母 $s$ 来表示行种类的变动。

直观地说，类型为$\operatorname{Row}(L)$的一行是一个从$\mathcal{L} \backslash L$到类型的函数。也就是说，$L$指定了行不得定义的标签集合。例如，(基本)类型$\Pi(\ell$ : int ; $\mathrm{x})$的类型为Type，如果$\mathrm{X}$的类型为$\operatorname{Row}(\{\ell\})$，那么行$(\ell$ : int ; $\mathrm{x})$的类型为$\operatorname{Row}(\emptyset)$。

为了保持抽象，行的定义通过一个签名 $\mathcal{S}_{0}$ 来构建基本类型，以及一个签名 $\mathcal{S}_{1}$ 来构建行。从这两个签名出发，我们定义了一个新的签名 $\mathcal{S}$，它完全指定了类型的集合。然而，签名 $\mathcal{S}$ 必须在两个输入签名 $\mathcal{S}_{0}$ 和 $\mathcal{S}_{1}$ 的（基本）种类之上叠加行种类。我们使用乘积签名来说明这个过程。更准确地说，我们从两个签名 $K \Rightarrow \kappa$ 和 $K^{\prime} \Rightarrow \kappa^{\prime}$ 构建一个乘积签名，并使用以下记法：我们用 $\kappa . \kappa^{\prime}$ 表示对 $\left(\kappa, \kappa^{\prime}\right)$；$K . \kappa$ 表示映射 $(d \mapsto K(d) . \kappa)^{d \in \operatorname{dom}(K)}$；$(K \Rightarrow \kappa) . \kappa^{\prime}$ 表示种类签名 $K . \kappa \Rightarrow \kappa . \kappa^{\prime}$；对称地，我们写出 $\kappa . K^{\prime}$ 和 $\kappa .\left(K^{\prime} \Rightarrow \kappa^{\prime}\right)$。签名 $\mathcal{S}$ 重新使用了与 $\mathcal{S}_{0}$ 和 $\mathcal{S}_{1}$ 相同的输入类型构造函数，但在不同的行种类上。我们使用上标来提供不同种类上的类型构造函数的副本，从而避免种类的重载。

1.11.4 定义[签名行的扩展]：设 $\mathcal{S}_{0}$ 和 $\mathcal{S}_{1}$ 是签名，其中 $\mathcal{S}_{1}$ 中的所有符号都是一元的。以 $\mathcal{S}_{1}$ 对 $\mathcal{S}_{0}$ 的行扩展是指如下定义的签名 $\mathcal{S}$，其中 $\kappa$ 遍历基本种类（即在 $\mathcal{S}_{0}$ 和 $\mathcal{S}_{1}$ 中使用的种类），而 $s$ 遍历行种类。

| $F \in \operatorname{dom}(\mathcal{S})$ | Signature | Conditions |
| :---: | :--- | :--- |
| $G^{s}$ | $(K \Rightarrow \kappa) . s$ | $(G: K \Rightarrow \kappa) \in \mathcal{S}_{0}$ |
| $H$ | K.Row $(\emptyset) \Rightarrow \kappa$. Type | $(H: K \Rightarrow \kappa) \in \mathcal{S}_{1}$ |
| $\partial^{\kappa, L}$ | $\kappa .($ Type $\Rightarrow \operatorname{Row}(L))$ |  |
| $\ell^{\kappa, L}$ | $\kappa .($ Type $\otimes \operatorname{Row}(\ell . L) \Rightarrow \operatorname{Row}(L))$ | $\ell \notin L$ |

我们通常写作 $\ell^{\kappa, L}: \mathrm{t}_{1}$; $\mathrm{t}_{2}$ 而不是 $\ell^{\kappa, L} \mathrm{t}_{1} \mathrm{t}_{2}$，并让这个符号具有右结合性。由于对于任何类型表达式 $\mathrm{T}$，指数可以从不带指数的类型构造器的种类中明确无误地恢复，我们经常省略类型构造器的上标。

1.11.5 示例：假设存在单一的基本种类 $\star$ 并且 $\mathcal{S}_{1}$ 包含一个独特的类型构造器 $\Pi$ （因此它的种类为 $\star \Rightarrow \star$ ）。行类型的一个例子是 $\mathrm{X}_{0} \rightarrow \Pi\left(\ell_{1}: G ;\left(\mathrm{Y} \rightarrow \partial \mathrm{x}_{0}\right)\right)$。带有所有上标注释的情况下，这个类型是

$$
\mathrm{X}_{0} \rightarrow^{\star, \text { Type }} \Pi\left(\ell_{1}^{\star, \text { Row }(\emptyset)}: G^{\text {Type }} ;\left(\mathrm{Y} \rightarrow^{\star, \text { Row }\left(\left\{\ell_{1}\right\}\right)} \partial^{\star, \text { Row }\left(\left\{\ell_{1}\right\}\right)} \mathrm{X}_{0}\right)\right) .
$$

直观地说，这是一种类型的函数，它接受一个类型为 $\mathrm{X}_{0}$ 的值，并返回一个记录，其中字段 $\ell_{1}$ 的类型为 $G$，而所有其他字段都是这样的函数：给定任意类型的值，它们会返回一个（相同）类型 $\mathrm{X}_{0}$ 的值。这种类型的一个实例是 $\mathrm{X}_{0} \rightarrow \Pi\left(\ell_{1}: G ;\left(\left(\ell_{2}: \mathrm{Y}_{2} ; \mathrm{Y}^{\prime}\right) \rightarrow\left(\ell_{2}: \mathrm{X}_{0} ; \partial \mathrm{X}_{0}\right)\right)\right)$，通过实例化行变量 $\mathrm{Y}$ 并展开常量行 $\partial \mathrm{X}_{0}$ 得到。如下所示，实际上这个类型等同于 $\mathrm{X}_{0} \rightarrow \Pi\left(\ell_{1}: G\right.$; $\left.\ell_{2}: \mathrm{Y}_{2} \rightarrow \mathrm{X}_{0} ;\left(\mathrm{Y}^{\prime} \rightarrow \partial \mathrm{X}_{0}\right)\right)$，这是由于类型构造函数 $\rightarrow$ 对类型构造函数 $\ell_{2}$ 的分配性质。请注意，$\mathrm{Y}$ 是一个行变量，可以展开为在不同标签上的不同类型变量，而 $\partial \mathrm{X}$ 是一个常量行，在所有标签上都展开为相同的类型变量 $\mathrm{X}$。

1.11.6 示例 [ 不当的表达式 ]：在先前示例的假设下，表达式 $\mathrm{X} \rightarrow \Pi(\mathrm{X})$ 不是一个行类型，因为变量 $\mathrm{X}$ 不能同时是行类型种类以及按照其从左到右两次出现所需的 $\operatorname{Row}(\emptyset)$。表达式 $\left(\ell: \mathrm{x} ; \ell: \mathrm{X}^{\prime} ; \mathrm{x}^{\prime \prime}\right)$ 也是不当的，因为内部表达式 $\left(\ell: \mathrm{X}^{\prime} ; \mathrm{X}^{\prime \prime}\right)$ 的行种类为 $\operatorname{Row}(L)$ 且 $\ell \notin L$ 不能同时也有行种类 $\operatorname{Row}(\{\ell\})$，正如整个表达式中其出现所要求的。实际上，行种类禁止对同一标签的多次定义，也禁止在基本类型的地方使用行，反之亦然。注意 $\Pi(\Pi(\mathrm{X}))$ 也是不合法的，因为 $\mathcal{S}_{1}$ 的类型构造器没有提升为行种类，因此除了在类型构造器 $\partial$ 下，不能在行中出现，作为基本类型。

1.11.7 练习 $[\star \star \star, \nrightarrow]$ ：设计一个算法，从类型的种类推断类型表达式中类型构造器的上标。类型的表达式的种类也能被推断吗？当省略类型构造器的上标和整个类型表达式的种类时，你能给出一个检查类型表达式是否良好种类的算法吗？

## Meaning of rows

如上所述，类型为 $\operatorname{Row}(L)$ 的一行代表从 $\mathcal{L} \backslash L$ 到类型的函数。实际上，在模型中将其明确表示为一个无限分支的树更为简单。为此，我们使用了一组构造函数 $L$，其（无限但可数）元数为 $\mathcal{L} \backslash L$。

1.11.8 定义 [行模型]：设 $\mathcal{S}$ 是通过签名 $\mathcal{S}_{1}$ 对签名 $\mathcal{S}_{0}$ 进行行扩展得到的。设 $\mathcal{S}_{\mathcal{M}}$ 是以下签名，其中 $\kappa$ 遍历基本种类，$L$ 遍历 $\mathcal{L}$ 的有限子集：

| $F \in \operatorname{dom}\left(\mathcal{S}_{\mathcal{M}}\right)$ | Signature | Conditions |
| :--- | :--- | :--- |
| $G$ | $(K \Rightarrow \kappa)$. Type | $(G: K \Rightarrow \kappa) \in \mathcal{S}_{0}$ |
| $H$ | K.Row $(\emptyset) \Rightarrow \kappa$. Type | $(H: K \Rightarrow \kappa) \in \mathcal{S}_{1}$ |
| $L^{\kappa}$ | $\kappa .($ Type $\mathcal{L} \backslash L \Rightarrow \operatorname{Row}(L))$ |  |

让 $\mathcal{M}_{\kappa}$ 由那些在签名 $\mathcal{S}_{\mathcal{M}}$ 上构建的正规树 $t$ 组成，使得 $t(\epsilon)$ 的像类型为 $\kappa$。我们将签名 $K \Rightarrow \kappa . s$ 中的类型构造器 $F$ 解释为一个函数，它将 $\mathcal{M}_{K}$ 中的 $T$ 映射到 $\mathcal{M}_{\kappa . s}$ 中的 $t$，这是通过对 $F$ 以及基本类型 $\kappa$ 进行案例分析来定义的。

| $F \in \mathcal{S}$ | $t(\epsilon)$ | For $d \in \operatorname{dom}(K)$ and $\ell \in \mathcal{L} \backslash L, \ell \neq \ell_{0}$. |
| :--- | :--- | :--- |
| $G^{\text {Type }}$ | $G$ | $t / d=T(d)$ |
| $H$ | $H$ | $t / 1=T(1)$ |
| $G^{\text {Row }(L)}$ | $L^{\kappa}$ | $t(\ell)=G \wedge t /(\ell \cdot d)=T(d) / \ell$ |
| $\partial^{\kappa, L}$ | $L^{\kappa}$ | $t / \ell=T(1)$ |
| $\ell_{0}^{\kappa, L}$ | $L^{\kappa}$ | $t / \ell_{0}=T(1) \wedge t / \ell=T(2) / \ell$ |

在存在子类型的情况下，我们让类型构造器$G$和$H$在$\mathcal{S}_{\mathcal{M}}$中的行为与$\mathcal{S}_{0}$和$\mathcal{S}_{1}$中一样，而类型构造器$L^{\kappa}$在每个位置上都是孤立的和协变的。以这种方式定义基本类型并解释类型构造器的模型称为行模型。

## 使用行类型的推理

在本节中，我们假设一个子类型模型。所有推理原则也适用于仅相等模型，这是子类型模型的一个子案例。

行的含义已经被仔细定义，以便独立于某些语法选择。特别是，重要字段类型的声明顺序不会改变行的含义。以下引理正式陈述了这一点。

1.11.9 引理：图1-17的方程等价于真。

证明：每个方程可以独立考虑。只需看到任何赋值函数 $\phi$ 都会将方程的两边映射到同一个元素上。

$$
\begin{align*}
\left(\ell_{1}: \mathrm{T}_{1} ; \ell_{2}: \mathrm{T}_{2} ; \mathrm{T}_{3}\right) & =\left(\ell_{2}: \mathrm{T}_{2} ; \ell_{1}: \mathrm{T}_{1} ; \mathrm{T}_{3}\right)  \tag{C-Row-LL}\\
\partial \mathrm{T} & =(\ell: \mathrm{T} ; \partial \mathrm{T})  \tag{C-Row-DL}\\
\partial\left(G \mathrm{~T}_{1} \ldots \mathrm{T}_{n}\right) & =G \partial \mathrm{T}_{1} \ldots \partial \mathrm{T}_{n}  \tag{C-Row-DG}\\
G\left(\ell: \mathrm{T}_{1} ; \mathrm{T}_{1}^{\prime}\right) \ldots\left(\ell: \mathrm{T}_{n} ; \mathrm{T}_{n}^{\prime}\right) & =\left(\ell: G \mathrm{~T}_{1} \ldots \mathrm{T}_{n} ; G \mathrm{~T}_{1}^{\prime} \ldots \mathrm{T}_{n}^{\prime}\right) \tag{C-Row-GL}
\end{align*}
$$

## 图1-17：行类型的等式推理。

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

## 图1-18：行约束等价定律。

在模型中，这直接源自行类型的含义。请注意，这个事实只依赖于类型的语义，而不是子类型谓词的语义。

从这些方程可以看出，类型构造器$\ell, \partial$和$G$永远不会孤立出现，每个方程都展示了一对兼容的顶级符号。类型构造器的变化性和不兼容的对取决于签名$\mathcal{S}_{0} \uplus \mathcal{S}_{1}$。然而，不难看出，类型构造器$\partial$和$\ell$在所有方向上逻辑上是共变的，且类型构造器$G$在$\operatorname{dom}\left(\mathcal{S}_{0} \uplus \mathcal{S}_{1}\right)$中的逻辑变化性对应于它们的语法变化性，在大多数情况下，这将允许分解具有相同顶级符号的方程。此外，如果两个项的顶级符号形成图1-17方程派生的四个兼容对之一，那么这两个项之间的等式只有在子表达式可以以某种方式“协调”时才成立。有一种与分解非常相似的转换，称为变异，它模仿了图1-17中行的方程，并由图1-18的规则描述。为了提高可读性和简洁性，我们用$\mathrm{T}_{i}^{I}$代替$\mathrm{T}_{i}^{i \in I}$。

1.11.10 引理 [突变]：图1-18中的所有等价定律成立。

Proof:

- 案例C-Mute-LL：设X \# ftv( $\left.\mathrm{T}_{1}, \mathrm{~T}_{1}^{\prime}, \mathrm{T}_{2}, \mathrm{~T}_{2}^{\prime}\right)(\mathbf{1})$ 且 $\ell_{1} \neq \ell_{2}$。设 $\operatorname{Row}(L)$ 为该方程的行类型。设 $\phi$ 是一个验证约束 $\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{T}_{1}^{\prime}\right)=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{T}_{2}^{\prime}\right)$ 的地面赋值。即，$\phi$ 将多方程的所有项发送到行类型 $\operatorname{Row}(L)$ 相同的地面上类型 $t$。此外，行项语义意味着 $t$ 满足 $t(\epsilon)=L, t / \ell_{1}=\phi\left(\mathrm{T}_{1}\right)=\phi\left(\mathrm{T}_{2}^{\prime}\right) / \ell_{1}, t / \ell_{2}=\phi\left(\mathrm{T}_{1}^{\prime}\right) / \ell_{2}=\phi\left(\mathrm{T}_{2}\right)$，且对于所有 $\ell \in \mathcal{L} \backslash \ell_{1} \cdot \ell_{2} . L$ (2)，$t / \ell=\phi\left(\mathrm{T}_{2}^{\prime}\right) / \ell=\phi\left(\mathrm{T}_{1}^{\prime}\right) / \ell$。设 $t^{\prime}$ 是由 $t^{\prime}(\epsilon)=\ell_{1} \cdot \ell_{2} . L$ 和对于所有 $\ell \in \mathcal{L} \backslash \ell_{1} \cdot \ell_{2} . L$，$t^{\prime} / \ell=t / \ell$ 定义的树。通过构造和 (2)，$\phi\left[\mathrm{X} \mapsto t^{\prime}\right]$ 满足两个方程 $\mathrm{T}_{1}^{\prime}=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{x}\right)$ 和 $\mathrm{T}_{2}^{\prime}=\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{x}\right)$。因此，通过CM-ExisTs和 (1)，$\phi$ 满足 $\exists \mathrm{X} \cdot \mathrm{T}_{1}^{\prime}=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{X}\right) \wedge \mathrm{T}_{2}^{\prime}=\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{X}\right)$。反之，我们有蕴含：

$$
\begin{align*}
& \exists \mathrm{X} .\left(\mathrm{T}_{1}^{\prime}=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{X}\right) \wedge \mathrm{T}_{2}^{\prime}=\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{X}\right)\right) \\
& \equiv \exists \mathrm{X} .\left(\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{T}_{1}^{\prime}\right)=\left(\ell_{1}: \mathrm{T}_{1} ; \ell_{2}: \mathrm{T}_{2} ; \mathrm{X}\right) \wedge\right. \\
&\left.\quad\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{T}_{2}^{\prime}\right)=\left(\ell_{2}: \mathrm{T}_{2} ; \ell_{1}: \mathrm{T}_{1} ; \mathrm{X}\right)\right)  \tag{3}\\
& \Vdash \exists \mathrm{X} .\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{T}_{1}^{\prime}\right)=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{T}_{2}^{\prime}\right)  \tag{4}\\
& \equiv\left(\ell_{1}: \mathrm{T}_{1} ; \mathrm{T}_{1}^{\prime}\right)=\left(\ell_{2}: \mathrm{T}_{2} ; \mathrm{T}_{2}^{\prime}\right) \tag{5}
\end{align*}
$$

（3）遵循$\ell_{1}$和$\ell_{2}$的协方差；（4）根据C-Row-LL和等价的传递性；（5）根据$\mathrm{C}-\mathrm{Ex} *$和（1）。

- C-Mute-LG、C-Mute-DG和C-Mute-DL案例：推理与C-Mute-LL案例相似。

## 在等式模型中解决行约束问题

在本节中，我们扩展了仅限于等式的自由树模型（图1-11）的约束求解器，以便处理行。因此，我们假设一个仅限等式的模型。

突变是在一大类由语法理论描述的非自由代数中求解方程的常见技术（Kirchner和Klay，1990年）。图1-17中的方程恰好是一个等式理论的语法表示，可以从中自动导出统一算法（Rémy，1993年）。我们不使用语法理论的结果，直接恢复相同的转换规则。

以下引理表明，所有没有变异规则的类型构造器对实际上是不可兼容的。

1.11.11 引理：所有符号 $H \in \mathcal{S}_{1}$ 都是孤立的。此外，对于每一对不同的类型构造器 $G_{1}, G_{2} \in \operatorname{dom}\left(\mathcal{S}_{0} \uplus \mathcal{S}_{1}\right)$ 和每一种行类型 $s$，都有 $G_{1}^{s} \bowtie G_{2}^{s}$。

证明：形式为 $H \overrightarrow{\mathrm{T}}$ 的项被解释为带有 $H$ 在出现 $\epsilon$ 位置的地面类型，反之，唯一解释带有 $H$ 在出现 $\epsilon$ 位置的类型的项就是形式 $H \overrightarrow{\mathrm{T}}$。因此，不可能有任何地面赋值可以永远。

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

## 图1-19：行类型的统一附录

将 $H \overrightarrow{\mathrm{T}}$ 和 $F \overrightarrow{\mathrm{T}^{\prime}}$ 发送到相同的地面术语，当 $F \neq H$ 时，结果是 $H$ 被孤立。

令$G_{1}$和$G_{2}$是$\mathcal{S}_{0}$的两个类型构造器。对于$s=$类型，形式为$G_{1}^{s} \overrightarrow{\mathrm{T}}$和$G_{2}^{s} \overrightarrow{\mathrm{T}}^{\prime}$的项的解释分别是带有符号$G_{1}$和$G_{2}$在出现$\epsilon$处的地面类型。因此，在任何地面赋值下，它们都不能被设置为相等。对于$s=\operatorname{Row}(L)$，形式为$G_{1}^{s} \overrightarrow{\mathrm{T}}$和$G_{2}^{s} \overrightarrow{\mathrm{T}}^{\prime}$的项的解释分别是带有构造器$L$在出现$\epsilon$处和构造器$G_{1}$和$G_{2}$在出现1处的地面类型。因此，在任何地面赋值下，它们也不能被设置为相等。

任何其他类型构造器的组合形成了兼容的对，如图1-17的方程所示，可以通过图1-18的变异规则进行转换。行项的约束求解器是由图1-11的重写规则定义的关系$\rightarrow^{\dagger}$，除了规则S-CLASH，它被图1-19的一组规则所取代。

1.11.12 引理：重写系统 $\rightarrow^{\dagger}$ 是强归约的。

请注意，$\rightarrow^{\dagger}$ 的终止依赖于类型具有良好的分类。特别是，在类型分类不良的方程系统 $\mathrm{X}=\ell: \mathrm{T} ; \mathrm{X}^{\prime} \wedge \mathrm{X}^{\prime}=\ell^{\prime}: \mathrm{T} ; \mathrm{X}$ 中，$\rightarrow^{\dagger}$ 不会终止。

1.11.13 引理：如果 $U \rightarrow^{\dagger} U^{\prime}$，那么 $U \equiv U^{\prime}$。

证明：只需独立地为每个定义 $\rightarrow^{\dagger}$ 的规则检查该属性。图1-11中的规则除S-CLASH之外的证明对行项同样有效。对于S-Decompose规则，它遵循所有类型构造器的不变性，这一点对于行项是保持的。对于规则S-CLASS-I，它遵循引理1.11.11，对于变异规则，它遵循引理1.11.10。

尽管缩减对于行类型来说并不严谨，因此不能用于行类型的计算，但它仍有一些意义。特别是，以下属性表明行类型的正常形式与常规类型的正常形式是相同的。

1.11.14 引理：对于 $\rightarrow^{\dagger}$ 的正规形式系统 $U$ 也是 $\rightarrow$ 的正规形式。

证明：唯一不在 $\rightarrow^{\dagger}$ 中的 $\rightarrow$ 规则是S-CLASH。因此，只需观察如果规则S-CLASH适用，那么规则S-CLASS-I 或者一个变异规则也同样适用。

作为一个推论，引理1.8.6扩展到行类型。

## 记录操作

我们现在举例说明在记录上使用行来进行类型检查操作。行最简单的应用是带有无限载体的完整记录。记录类型用行表示，而不是简单的积类型。基本操作与有限情况下的操作相同，即创建、多态更新和多态访问，但现在标签取自一个无限集。然而，创建和多态更新，其中析构函数现在被视为构造函数，并用于将记录表示为关联列表。访问记录$v$在字段$\ell$处的值，是通过线性搜索$v$中字段$\ell$的定义，并返回该定义，如果在$\ell$中没有找到定义，则返回默认值。

1.11.15 示例 [完整记录]：我们在 $\mathcal{S}_{1}$ 中假设有一个唯一的基本种类 $\star$ 和一个唯一的协变孤立类型构造器 $\Pi$。设 $\{\cdot\}$ 为一个一元构造器，$(\{\cdot \text { with } \cdot=\ell\})^{\ell \in \mathcal{L}}$ 为一组二元构造器集合，以及 $(\ell .\{\cdot\})^{\ell \in \mathcal{L}}$ 为一组一元析构器，具有以下归约规则：

$$
\begin{array}{rllr}
\{\mathrm{v}\} \cdot\{\ell\} & \xrightarrow{\delta} & \mathrm{v} & \\
\{\mathrm{w} \text { with } \ell=\mathrm{v}\} \cdot\{\ell\} & \xrightarrow{\delta} & \mathrm{v} & \\
\left\{\mathrm{w} \text { with } \ell^{\prime}=\mathrm{v}\right\} \cdot\{\ell\} & & \\
& \mathrm{w} .\{\ell\} & \text { if } \ell \neq \ell^{\prime} & \text { (RD-DEFAULT) } \\
\text { (RD-FOLLOw) }
\end{array}
$$

让初始环境 $\Gamma_{0}$ 包含以下绑定

$$
\begin{aligned}
\{\cdot\}: & \forall \mathrm{X} . \mathrm{X} \rightarrow \Pi(\partial \mathrm{X}) \\
\{\cdot \text { with } \ell=\cdot\}: & \forall \mathrm{XX} \mathrm{Y} . \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}^{\prime} \rightarrow \Pi\left(\ell: \mathrm{X}^{\prime} ; \mathrm{Y}\right) \\
\cdot\{\ell\}: & \forall \mathrm{XY} . \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}
\end{aligned}
$$

1.11.16 练习 [完整记录, $\star \star \star, \nrightarrow$] ：检查这些定义是否符合定义1.7.6的要求。

1.11.17 练习 [字段交换，$\star \star$ ]：向记录中添加一个操作以交换两个字段：给出简化规则和类型假设，并检查定义1.7.6的要求是否得到保持。

1.11.18 练习 [记录的正常形式，$\star \star \star \star$ ]：记录值可能包含重复。例如，$\left\{\{\mathrm{w}\right.$ with $\ell=\mathrm{v}\}$ with $\left.\ell=\mathrm{v}^{\prime}\right\}$ 实际上是一个与 $\left\{\mathrm{w}\right.$ with $\left.\ell=\mathrm{v}^{\prime}\right\}$ 观察等价的价值。同样，当 $\ell^{\prime} \neq \ell$ 时，两个记录值 $\left\{\{\mathrm{w}\right.$ with $\ell=\mathrm{v}\}$ with $\left.\ell^{\prime}=\mathrm{v}^{\prime}\right\}$ 和 $\left\{\left\{\mathrm{w}\right.\right.$ with $\left.\ell^{\prime}=\mathrm{v}^{\prime}\right\}$ with $\left.\ell=\mathrm{v}\right\}$ 也是如此。修改语义，使得相同类型的两个记录值具有相似的结构，且记录不包含无法访问的值。

1.11.19 练习 [映射应用，$\star \star$ ]：添加一个二元运算映射，使得表达式 (map v $\mathrm{w}$ ). $\{\ell\}$ 和 v. $\{\ell\}$ w. $\{\ell\}$ 对于每个标签 $\ell$ 都简化为相同的值。

1.11.20 练习 $[\star, \nrightarrow]$ ：到目前为止，完整的记录几乎都是常数。这种条件对于值来说不是必需的，只对类型是必需的。作为一个例子，引入一个原始记录，即一个nullary记录构造器，它将每个标签映射到不同的整数。给出其类型假设并回顾记录的语义。

与完整记录相比，标准记录是局部的，它们的域是有限的（但具有无限的载体）并且从它们的类型静态确定。可以通过在有限数量的字段上扩展空记录来构建标准记录。我们将这种记录称为具有多态扩展的记录。通过将编码到完整记录中的方式，可以获得具有多态扩展的记录，就像在有限情况下一样。

1.11.21 示例 [多态扩展的编码]：重新使用为有限情况引入的两个类型定义abs和pre，我们让abs编码一个未定义的字段，而prev编码一个具有值v的字段。我们使用以下语法糖及其含义和主要类型：

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

1.11.22 练习（推荐，$\star$）：扩展可能会实际上覆盖一个已存在的字段。你能定义一个版本多态的扩展，以防止这种情况发生吗？添加一个操作，隐藏记录中的一些特定字段。

可扩展记录也可以直接实现，无需编码成完整的记录。实际上，这只需要对完整记录进行微小的变化。

1.11.23 示例 [具有多态扩展的记录]：设 $\star$ 和 $\diamond$ 为两种基本类型。基本签名 $\mathcal{S}_{0}$ 包含（除了 $\rightarrow$ ）协变孤立类型构造器 pre 类型为 $\star \Rightarrow \diamond$ 和 abs 类型为 $\diamond$。在存在子类型的情况下，我们可以假设 pre $\leqslant$ abs。设 $\mathcal{S}_{1}$ 包含唯一的协变孤立类型构造器 $\Pi$ 类型为 $\diamond \Rightarrow \star$。设 \langle\rangle 为一元构造器，$\left(\{\cdot \text { with } \cdot=\ell)^{\ell \in \mathcal{L}}\right.$ 为二元构造器，以及 $(\ell .\{\cdot\})^{\ell \in \mathcal{L}}$ 为具有以下归约规则的一元析构器：

$$
\begin{aligned}
& \langle\mathrm{w} \text { with } \ell=\mathrm{v}\rangle .\langle\ell\rangle \quad \xrightarrow{\delta} \quad \mathrm{v} \quad \text { (ER-FOUnd) } \\
& \left\langle\text { w with } \ell^{\prime}=\mathrm{v}\right\rangle .\langle\ell\rangle \quad \xrightarrow{\delta} \quad \text { w. }\{\ell\} \quad \text { if } \ell \neq \ell^{\prime} \quad \text { (ER-FOLLOw) }
\end{aligned}
$$

让 $\Gamma_{0}$ 包含以下类型假设：

$$
\begin{aligned}
\langle\rangle: & \Pi(\partial \mathrm{abs}) \\
\langle\cdot \text { with } \ell=\cdot\rangle & \forall \mathrm{XX} \mathrm{Y} . \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}^{\prime} \rightarrow \Pi\left(\ell: \text { pre } \mathrm{X}^{\prime} ; \mathrm{Y}\right) \\
\cdot\langle\ell\rangle: & \forall \mathrm{XY} . \Pi(\ell: \text { pre X } ; \mathrm{Y}) \rightarrow \mathrm{X}
\end{aligned}
$$

注意，直接方法获得的打字假设与示例1.11.21中编码成完整记录所获得的是相同的。

1.11.24 练习 $[\star \star \star \star, \nrightarrow]$ ：证明直接语义与通过具有默认值的记录编码的语义之间的等价性。

1.11.25 练习 [推荐, $\star \star, \nrightarrow$ ]：证明可扩展记录的类型安全性在子类型模型和仅等式模型中都成立。

1.11.26 练习 [推荐, $\star, \nrightarrow$ ]：检查在子类型中，具有更多字段的记录可以替代具有较少字段的记录。检查在仅考虑相等性的模型中并非如此。

1.11.27 示例 [记录类型的细化]：在仅等价的模型中，包含更多字段的记录不能替代包含较少字段的记录。然而，通过对类型结构的微小细化，这可能部分得到恢复。字段的存在实际上可以从它们的类型中分离出来，从而在字段本身类型固定的情况下，允许对字段存在的一些多态性。设o是一种新的基本种类。设类型构造器abs和pre都属于种类$\circ$，并且设$\cdot$是一种新的类型构造器，其种类为$\circ \otimes \star \Rightarrow \diamond$。设$\Gamma_{0}$包含以下类型假设：

$$
\begin{aligned}
\langle\rangle: & \forall \mathrm{X} . \Pi(\partial(\text { abs } \cdot \mathrm{X})) \\
\langle\cdot \text { with } \ell=\cdot\rangle: & \forall \mathrm{ZXX}^{\prime} \mathrm{Y} . \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}^{\prime} \rightarrow \Pi\left(\ell: \mathrm{Z} \cdot \mathrm{X}^{\prime} ; \mathrm{Y}\right) \\
\cdot\langle\ell\rangle: & \forall \mathrm{XY} . \Pi(\ell: \operatorname{pre} \cdot \mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}
\end{aligned}
$$

记录的语义保持不变。新的签名严格推广了以前的签名（严格来说更多的程序可以被类型检查），同时保持了类型的健全性。这里有一个程序现在可以被类型检查，而之前则不能：

$$
\text { (if } a \text { then }\left\langle\left\langle\langle\rangle \text { with } \ell^{\prime}=\text { true) with } \ell=1\right\rangle \text { else }\langle\langle\rangle \text { with } \ell=2\rangle \text { ). }\langle\ell\rangle\right.
$$

请注意，当一个现有字段被遗忘时，字段的类型并没有被遗忘。因此，定义了相同字段但类型不兼容的两个记录仍然不能混合，这在子类型模型中是可能的。

1.11.28 示例 [精致子类型化]：在子类型化模型的情况下，对等式模型的前一次精化并不是很有趣。

子类型假设 pre $\leqslant$ abs 让 abs 在字段中扮演 $T$ 的角色。也就是说，abs 编码的是信息的缺失，而不是缺失的信息。换句话说，字段 $\ell$ 具有类型 abs 的值可能未定义或在该字段 $\ell$ 上定义；在后一种情况下，字段 $\ell$ 实际上已定义的事实只是被遗忘了。因此，类型只提供了记录实际域的一个下界近似。与仅基于等价的模型相比，这降低了精度，在后者中，记录的域可以从其类型得知。因此，一些只有在静态知道记录的确切域时才可能的记录表示优化就丢失了。

幸运的是，有一种方法可以恢复这种准确性。一个保守的解决方案当然是放弃不等式前缀 $\leqslant$ abs。请注意，这仍然会比使用等式模型更具表现力，因为例如 $\Pi(\ell$ : pre $\left(\mathrm{T}_{1} \rightarrow \mathrm{T}_{2}\right) ; \mathrm{T}\right) \leq \Pi(\ell$ : pre $\top ; \mathrm{T})$ 仍然成立，只要 $\rightarrow \leq \top$ 成立。这个解决方案被称为仅深度子类型化记录，而之前的解决方案提供了深度和宽度记录子类型化。相反，也可以保持宽度子类型化并禁止深度子类型化，通过保持关系 pre $\leqslant$ abs 同时要求 pre 不变；在这种情况下，可以整体忽略字段的存在的，但只要字段仍然可见，字段的类型就不能被弱化。

另一个更有趣的解决方案在于引入另一种类型构造器，其签名可以是 $\diamond$，并假设 pre $\leqslant$ either 且 abs $\leqslant$ either（但 pre $\nless$ abs）。在这里，either 在字段中扮演 $T$ 的角色，意味着字段要么是存在的（但被遗忘），要么是缺失的。而 abs 真正意味着缺失。类型检查的准确性可以正式表述为这样一个事实：类型为 $\Pi(\ell$ : abs $; \mathrm{T})$ 的记录值不能定义字段 $\ell$。

1.11.29 示例[混合子类型化]：我们很容易想把所有1.11.28示例的变化形式混在一起。作为第一次尝试，我们可以假设基本签名 $\mathcal{S}_{0}$ 包含共变类型构造器 pre 和 maybe 以及不变类型构造器 pre $_{=}$ 和 maybe $=$，它们的类型种类都是 $\star \Rightarrow \diamond$，还有两个类型构造器 abs 和 either，它们的类型种类是 $\diamond$，并且子类型顺序 $\leqslant$ 是由以下图表定义的：

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-133.jpg?height=285&width=436&top_left_y=939&top_left_x=948)

直观上，我们希望pre $=$ 和 maybe $=$ 在逻辑上是不变的，pre 和 maybe 在逻辑上是协变的，并且等价关系 pre $=\mathrm{T} \leq$ maybe $_{=} \mathrm{T}^{\prime} \equiv \mathrm{T}=\mathrm{T}^{\prime}$ 和

$$
\begin{equation*}
\text { pre }=\mathrm{T} \leq \text { pre } \mathrm{T}^{\prime} \equiv \text { pre } \mathrm{T} \leq \text { maybe } \mathrm{T}^{\prime} \equiv \text { maybe }_{=} \mathrm{T} \leq \text { maybe } \mathrm{T}^{\prime} \equiv \mathrm{T} \leq \mathrm{T}^{\prime} \tag{1}
\end{equation*}
$$

同时持有。然而，（1）要求例如类型构造器pre $=$和pre具有相同的方向，这在目前是不可能的，因为它们不具有相同的变异性。有趣的是，通过为每个类型构造器分配方向的可变性，并相应地定义结构子类型（参见练习1.11.30），这个限制可能被放宽。然后，在$\Gamma_{0}$中用pre $=$替换所有pre的出现，可以保持类型的健全性，并在同一设置下允许精确的记录类型和灵活的子类型。

1.11.30练习[宽松变量, $\star \star \star, \nrightarrow$]：设$\emptyset$可以作为新的变量，扩展例1.3.9中定义的变量组合，记$\nu \emptyset=\emptyset$，并且$\leqslant \emptyset$表示类型构造器上的全关系。现在，每个具有签名$K \Rightarrow \kappa$的类型构造器$F$都带有一个从$\operatorname{dom}(K)$到变量映射$\vartheta(F)$。定义$\vartheta\left(t, t^{\prime}, \pi\right)$为两个地面类型$t$和$t^{\prime}$在路径$\pi$上的变量，递归定义为$\vartheta\left(t, t^{\prime}, d \cdot \pi\right)=$ $\left(\vartheta(t(\epsilon))(d) \cap \vartheta\left(t^{\prime}(\epsilon)\right)(d)\right) \vartheta\left(t / d, t^{\prime} / d, \pi\right)$，且$\vartheta\left(t, t^{\prime}, \epsilon\right)=+$。然后以下定义子类型的解释：如果$t, t^{\prime} \in \mathcal{M}_{\kappa}$，则只有当对所有路径$\pi \in \operatorname{dom}(t) \cap \operatorname{dom}\left(t^{\prime}\right)$，$t(\pi) \leqslant^{\vartheta\left(t, t^{\prime}, \pi\right)} t^{\prime}(\pi)$成立时，$t \leq t^{\prime}$才成立。

检查关系 $\leq$ 仍然是一个偏序关系。检查已声明为协变（分别对应逆变、不变）的类型构造器在 $d$ 方向上逻辑上仍然是协变（分别对应逆变、不变）的。

记录拼接

记录连接会取两个记录并将它们组合成一个新的记录，其字段来源于定义它们的任意参数。当然，当两个记录不具有不相交的定义域时，就会存在歧义，此时应该做出选择以消除此类情况的不明确性。对称连接在这种情况下让连接未定义（Harper和Pierce，1991年），而非对称连接则让一侧（通常是右侧）始终优先。尽管记录连接的语义相当简单，但其类型判断仍然很难（无论是严格的还是优先级语义）。在例如（Wand，1989年；Rémy，1992年；Pottier，2000年）中可以找到关于记录连接的类型推论解决方案。

多态变体

变体可以通过代数数据类型定义来定义。然而，作为记录的字段，变体标签来自一个相对较小、有限的标签集合，两个变体定义将具有不兼容的类型。因此，为了保持兼容性，两个变体必须选择一个更大的集合中的标签，这个集合是所有可能标签的超集。一般来说，这降低了类型的准确性，并强制进行无用的动态标签检查，否则这些标签本可以知道不会出现。可扩展变体（第93页）允许使用任意大的标签集合，但并没有提高准确性。多态变体指的是一种更精确的变体类型检查机制，其中类型更准确地描述了实际可能出现的标签。它们允许从大量、潜在无限的预定义标签集合中构建和类型的值，并调用多态函数来探索它们。对于记录，这个问题可以通过首先分别考虑基于有限集合标签构建的变体的多态操作和具有无限标签集合的总变体，然后将两种方法结合起来来解决。我们提出了一个直接解决方案，通过与记录的简单类比。

确实，类型构造器pre可以用来区分变体可能实际携带的（有限）标签集合，与那些确定不会出现并用abs标记的标签。例如，一个变体$\ell$.v，由一个带有构造器标签$\ell$（arity为1）的值$\mathrm{v}$构建，可以赋予它主要类型方案$\forall \mathrm{X} . \Sigma(\ell:$ pre $\mathrm{T} ; \mathrm{X})$，其中$\mathrm{T}$是$\mathrm{v}$的类型。一元类型构造器$\Sigma$用于将行强制转换为变体类型——因此，变体类型和记录类型可能共享相同的内部行结构，并通过它们的顶部符号简单地区分。这种多态类型的一个实例是$\forall \mathrm{X} . \Sigma(\ell$ :pre $\mathrm{T}$; abs $)$，它表示变体必须用标签$\ell$构建，没有其他标签，因此保留了关于值形状的确切信息。变体多态类型的另一个实例是$\Sigma\left(\ell:\right.$ pre $\mathrm{T} ; \ell^{\prime}:$ pre $\mathrm{T}^{\prime}$; abs $)$。确实，假设值也可能用其他$\operatorname{tag} \ell^{\prime}$构建是合理的，即使我们知道实际上并非如此。有趣的是，这两个值$\ell$.v和$\ell^{\prime}$.v都有这个类型，并且可以在这种类型下混合。

我们使用过滤器来探索变体。一个过滤器 $\left[\ell: \mathrm{v} \mid \mathrm{v}^{\prime}\right]$ 是一个期望变体参数的函数，因此形式为 $\ell^{\prime}$.w。然后它继续进行 $\mathrm{v} \mathrm{w}$（如果 $\ell^{\prime}=\ell$），否则进行 $\mathrm{v}^{\prime} \mathrm{w}$。此过滤器的类型是 $\Sigma\left(\ell:\right.$ pre $\left.\mathrm{T} ; \mathrm{T}^{\prime}\right) \rightarrow \mathrm{T}^{\prime \prime}$，其中 $\mathrm{T}$ 是 $\mathrm{v}$ 接受的值的类型，$\Sigma\left(\ell: \mathrm{T}^{\prime \prime \prime} ; \mathrm{T}^{\prime}\right)$ 是 $\mathrm{v}^{\prime}$ 接受的值的类型，而 $\mathrm{T}^{\prime \prime}$ 是 $\mathrm{v}$ 和 $\mathrm{v}^{\prime}$ 都返回的值的类型。任何类型 $\mathrm{T}^{\prime \prime \prime}$ 都可以，尤其是 abs。实际上，当 w 传递给 $\mathrm{v}^{\prime}$ 时，已知它不具有标签 $\ell$，因此 $\mathrm{v}^{\prime}$ 对 $\ell$ 的行为无关紧要。可以为 $\mathrm{v}^{\prime}$ 使用空过滤器 []。这个过滤器实际上不应该被应用，我们通过分配 $\square$ 类型 $\forall \mathrm{X} . \Sigma(\partial \mathrm{abs}) \rightarrow \mathrm{X}$ 来确保这一点，因为没有变体值的类型是 $\Sigma(\partial \mathrm{abs})$。例如，过滤器 $\left[\ell: \mathrm{v}_{\ell} \mid\left[\ell^{\prime}: \mathrm{v}_{\ell^{\prime}} \mid[]\right]\right]$，可以简写为 $\left[\ell: \mathrm{v}_{\ell} \mid \ell^{\prime}: \mathrm{v}_{\ell^{\prime}}\right]$，可以应用于 $\ell$.v 或 $\ell^{\prime} . \mathrm{v}^{\prime}$。以下示例形式化了多态变体。

1.11.31 示例 [多态变体]：设 $\star$ 和 $\diamond$ 是两种基本类型。除了箭头类型构造器之外，设 $\mathcal{S}$ 还包含两种类型构造器，pre 的类型为 $\star \Rightarrow \diamond$，abs 的类型为 $\diamond$。在子类型存在的情况下，我们可以假设 abs $\leqslant$ pre。设 $\mathcal{S}_{1}$ 包含唯一的一个协变孤立类型构造器 $\Sigma$，其类型为 $\diamond \Rightarrow \star$。设 $\Gamma_{0}$ 由一元构造器 $(\ell . \cdot)^{\ell \in \mathcal{L}}$ 和原始操作 [，其 arity 为 0 以及 $([\ell: \cdot \mid \cdot] \cdot)^{\ell \in \mathcal{L}}$，其 arity 为 3 组成，并给出以下归约规则：

$$
\begin{aligned}
& {\left[\ell: \mathrm{v} \mid \mathrm{v}^{\prime}\right] \ell . \mathrm{w} \quad \xrightarrow{\delta} \quad \mathrm{v} \mathrm{w}} \\
& {\left[\ell: \mathrm{v} \mid \mathrm{v}^{\prime}\right] \ell^{\prime} . \mathrm{w} \quad \xrightarrow{\delta} \quad \mathrm{v}^{\prime} \mathrm{w} \quad \text { if } \ell \neq \ell^{\prime}}
\end{aligned}
$$

包含以下输入假设：

$$
\begin{aligned}
\ell . \cdot: & \forall \mathrm{XY} . \mathrm{X} \rightarrow \Sigma(\ell: \text { pre } \mathrm{X} ; \mathrm{Y}) \\
{[]: } & \forall \mathrm{X} . \Sigma(\partial \mathrm{abs}) \rightarrow \mathrm{X} \\
{[\ell: \cdot \mid \cdot]: } & \forall \mathrm{XX}^{\prime} \mathrm{YY} \mathrm{Y}^{\prime} .(\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow\left(\Sigma\left(\ell: \mathrm{X}^{\prime} ; \mathrm{Y}^{\prime}\right) \rightarrow \mathrm{Y}\right) \rightarrow \Sigma\left(\ell: \operatorname{pre} \mathrm{X} ; \mathrm{Y}^{\prime}\right) \rightarrow \mathrm{Y}
\end{aligned}
$$

1.11.32 练习 [可扩展变体的健全性，$\star \star \star \star, \nrightarrow$ ]：证明在仅相等性和子类型模型中，可扩展变体的类型健全性。

## 行的其他应用

多态记录和变体是行（rows）最知名的应用。除了它们呈现方式的许多变化——我们仅说明了其中一些——行还有其他几个有趣的应用。

自从对象可以被看作是函数记录，至少从类型的角度来看是这样，行也可以用来类型结构化对象（Wand, 1994; Rémy, 1994; Rémy和Vouillon, 1998），特别是提供多态方法调用。这是在Objective Caml中类型检查对象的关键（Rémy和Vouillon, 1998）。一等消息（Nishimura, 1998; Müller和Nishimura, 1998; Pottier, 2000）以有趣的方式结合了记录和变体：虽然变体类型的过滤器强制所有分支具有相同的返回类型，但一等消息将过滤器视为函数记录（也称为对象），而不是从变体类型到共享返回类型的函数。消息是变体类型的一个元素。将对象应用于消息，即从函数记录到变体类型的应用，从记录中选择与消息标签相同的分支，并将其应用于消息的内容，这与模式匹配类似。然而，这些应用通过首先将记录的域限制为消息可能携带的标签集合，从而更精确地进行类型检查，因此其他分支尤其是它们的返回类型不受约束。

行类型也可能代表类型内的属性集合或类型细化，并可用于程序分析的类型系统中。值得提及的两个例子是它们在软类型（Cartwright和Fagan，1991；Wright和Cartwright，1994）和未捕获异常的类型检查（Leroy和Pessaux，2000）中的应用。

关键在于将行标签集合分解为某一类有限分区的闭包，这些分区可以通过某些操作来组合。在这里，这些分区由单例标签和余有限标签集合组成；操作包括将单例标签与余有限标签集合合并（或者相反地拆分）。还可能有其他的分解方式，例如，可以想象将标签考虑在二维空间中。更一般地，标签也可能具有内部结构，例如，可以考虑自动机作为标签。还要注意，记录类型是分层的，因为行（即类型为$\operatorname{Row}(L)$的表达式）本身可能不包含记录 - $\mathcal{S}_{1}$的构造函数只给出了图像行类型的Type。这个限制可以部分地放宽，导致行度数的增加（Rémy, 1992b）...以及复杂性的增加！更有趣的是类型索引行，其中标签本身就是类型（Shields和Meijer, 2001）。

## 行的替代品

最初使用行（rows）来描述可扩展记录类型的想法归功于Wand（Wand, 1987, 1988）。对行类型（row types）的一个关键简化是使它们成为从标签到类型的总函数，并在字段的结构中明确编码确定性，例如使用pre和abs类型构造函数，正如这里所展示的。这种分解将统一约束的解析简化为简单的等式推理（Rémy, 1993, 1992a）。其他不将行视为总函数的方法似乎更显得临时性，并且通常有硬性限制（Jategaonkar和Mitchell, 1988; Ohori和Buneman, 1989; Berthomieu, 1993; Ohori, 1999）。在这些部分解决方案中，（Ohori, 1999）在对多态访问单独需要的情况下，由于其整体简单性而相当有趣。行和字段也可以在临时类型约束中表示，而不是项和等式（或子类型）约束。例如，合格类型使用谓词（T具有ℓ: T'）和（T缺少ℓ）来表示行T的字段ℓ定义为类型T'或未定义（Jones, 1994b; Odersky, Sulzmann和Wehr, 1999b）。实际上，在我们的等式模型中，这些约束等价于存在X . T=（ℓ: pre T' ; X）和存在X . T=（ℓ: abs ; X）。记录类型检查在子类型存在的情况下也得到了广泛研究。通常，记录子类型是直接给出的，而不是通过行。尽管这些解决方案非常具有表现力，得益于子类型，但它们仍然受到非结构性记录类型处理的影响，不能类型行扩展。因此，即使在子类型模型中，使用行也增加了表现力，通常也是一个简化。然后子类型模型也可以利用增加类型构造函数pre和abs的结构并借助子类型相关联的可能性（Pottier, 2000）。请注意，尽管行是为了类型推断而引入的，但它们似乎对显式类型语言也有益，因为即使是其他高级解决方案（Cardelli和Mitchell, 1991; Cardelli, 1992）也是有限的。

图1-19的规则是解决行类型约束的一种方法。在带有子类型约束的模型中，基于闭包的更直接的解析可能更为合适（Pottier，2003）。

选定练习的B解决方案

1.2.6 解决方案：这个定义并没有按预期工作，因为if是一个析构器，其参数根据ML-演算的按值调用语义，在R-TRUE或R-FALSE被允许触发之前会被求值。因此，表达式if $t_{0}$ then $t_{1}$ else $t_{2}$的语义是在选择其中一个之前先对$t_{1}$和$t_{2}$进行求值。由于这些表达式可能有副作用（例如，它们可能无法终止，或者更新一个引用），这种语义是不希望出现的。可以通过将$t_{1}$和$t_{2}$放入闭包中来获得所需的求值顺序，这会延迟它们的求值，然后调用条件表达式返回的闭包，强制其主体进行求值。换句话说，表达式if $t_{0}$ then $t_{1}$ else $t_{2}$现在应该被视为语法糖，用于if $t_{0}\left(\lambda\right.$ z.t $\left._{1}\right)\left(\lambda z . t_{2}\right) \hat{0}$。常量$\hat{0}$的选择是任意的，因为它会被丢弃；任何值都可以。

1.2.21 解：在Damas和Milner的类型系统中，我们有：

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-140.jpg?height=193&width=905&top_left_y=827&top_left_x=688)

请注意，因为 $\mathrm{X}$ 在环境 $\mathrm{z}_{1}: \mathrm{X}$ 中自由出现，所以无法以非平凡的方式将 DM-GEN 应用于判断 $z_{1}: X \vdash z_{1}: X$。因此，$z_{2}$ 不能接收类型方案 $\forall x$.X，整个表达式也不能接收类型 $\mathrm{X} \rightarrow \mathrm{Y}$，其中 $\mathrm{X}$ 和 $\mathrm{Y}$ 是不同的。

1.2.22 解：很容易证明恒等函数具有类型 int → int：

$$
\frac{\overline{\Gamma_{0} ; z: \text { int } \vdash \mathrm{z}: \text { int }}}{\Gamma_{0} \vdash \lambda \mathrm{z} . \mathrm{z}: \text { int } \rightarrow \text { int }} \text { DM-ABS }
$$

实际上，这种类型推导中没有任何内容依赖于将$z$的类型选择为int。因此，我们完全可以使用类型变量$X$来代替。此外，在形成了箭头类型$\mathrm{X} \rightarrow \mathrm{X}$之后，我们可以使用DM-GEN规则来对$\mathrm{X}$进行普遍量化，因为它不再出现在环境中。

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-140.jpg?height=191&width=824&top_left_y=1708&top_left_x=728)

值得注意的是，尽管类型推导使用了一个任意的类型变量X，但最终的类型判断没有自由类型变量。因此，它与x的选择无关。在以下内容中，我们将上述类型推导称为Δ₀。

接下来，我们证明在初始环境$\Gamma_{0}$下，后继函数具有类型int $\rightarrow$ int。我们用$\Gamma_{1}$表示$\Gamma_{0} ; z$ : int，并使用隐含的DM-VAR。

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-141.jpg?height=252&width=956&top_left_y=466&top_left_x=680)

在以下内容中，我们将上述类型推导称为 $\Delta_{1}$。我们现在可以为第三个类型判断构建一个推导。我们用 $\Gamma_{2}$ 表示 $\Gamma_{0} ; f$ : int $\rightarrow$ int。

$$
\frac{\Delta_{1} \frac{\Gamma_{2} \vdash \mathrm{f}: \text { int } \rightarrow \text { int } \quad \Gamma_{2} \vdash \hat{2}: \text { int }}{\Gamma_{2} \vdash \mathrm{f} \hat{2}: \text { int }}}{\Gamma_{0} \vdash \text { let } \mathrm{f}=\lambda \mathrm{z} \cdot \mathrm{z} \hat{+} \hat{1} \text { in } \mathrm{f} \hat{2}: \text { int }} \text { DM-LET }
$$

为了推导出第四个类型判断，我们重新使用 $\Delta_{0}$，这证明了恒等函数具有多态类型。我们用 $\Gamma_{3}$ 表示 $\Gamma_{0} ; f: \forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$。通过 DM-VAR 和 DM-INST，我们得到 $\Gamma_{3} \vdash \mathrm{f}:($ int $\rightarrow$ int $) \rightarrow($ int $\rightarrow$ int) 以及 $\Gamma_{3} \vdash f:$ int $\rightarrow$ int。因此，我们可以构建以下推导：

$$
\begin{aligned}
& \Gamma_{3} \vdash \mathrm{f}:(\text { int } \rightarrow \text { int }) \rightarrow(\text { int } \rightarrow \text { int })
\end{aligned}
$$

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-141.jpg?height=256&width=846&top_left_y=1290&top_left_x=806)

第一个和第三个判断在简单类型的λ-演算中是有效的，因为它们既不使用DM-GEN也不使用DM-INST，仅使用DM-LET来向环境中引入单态绑定 f: int -> int。当然，第二个判断无效：因为它涉及到非平凡类型方案，它在简单类型的λ-演算中甚至不是一个良好形成的判断。第四个判断在简单类型的λ-演算中是良好形成的，但不可推导。这是因为在表达式 f f 2^ 中，f被用在两种不兼容的类型上，即 (int -> int) -> (int -> int) 和 int -> int。这两种类型都是环境中分配给f的类型方案 ∀X . X -> X 的实例，在环境 Γ_3 中。

通过检查DM-VAR、DM-GEN和DM-INST，可以直观地看出，如果可以从$\Gamma_{0} \vdash \hat{1}: \mathrm{T}$推导出来，那么$\mathrm{T}$必须是整型（int）。由于整型不是箭头类型，表达式$\hat{1} \hat{2}$在$\Gamma_{0}$下不能被良好地类型化。实际上，由于这个表达式是停顿的，它在一个健全的类型系统中不能被良好地类型化。

表达式 $\lambda f$. $(f f)$ 在简单类型的 $\lambda$-演算中类型不正确，因为没有类型 $\mathrm{T}$ 可以与形式 $\mathrm{T} \rightarrow \mathrm{T}^{\prime}$ 的类型相同。实际上，$\mathrm{T}$ 随后会是其自身的子项。同样地，这个表达式在 $\mathrm{DM}$ 中也是类型不正确的。实际上，检查 DM-GEN 和 DM-INST 的存在并没有区别：只要环境中有绑定 $f: T$，DM-GEN 就不能泛化 $\mathrm{T}$，而 DM-INST 只能将 $T$ 实例化为它自己。因此，只有在 $f$ 是 let 绑定而不是 $\lambda$ 绑定时，自应用 $f f$ 在 DM 中才是类型正确的。这个论证关键在于 $f$ 必须分配一个单型。实际上，表达式 $\lambda f .(f f)$ 在 System F 的一个隐式类型变体中是类型正确的：它的一个类型是 $(\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}) \rightarrow(\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X})$。这也依赖于类型的有限性：实际上，在这个表达式中，扩展了简单类型 $\lambda$ 演算并带有递归类型的系统中是类型正确的，其中方程 $\mathrm{T}=\mathrm{T} \rightarrow \mathrm{T}^{\prime}$ 有解。

1.2.23 解：很明显，DM-GEN的效果可以通过一系列连续应用DM-GEN'来获得。反之，考虑一个DM-GEN'的实例，其前提是 $\Gamma \vdash \mathrm{t}: \mathrm{S}(\mathbf{1})$ 和 $\mathrm{X} \notin f t v(\Gamma)$ （2）。让我们记 $\mathrm{S}=\forall \overline{\mathrm{X}} . \mathrm{T}$，其中 $\overline{\mathrm{X}} \# f t v(\Gamma)$ （3）。将DM-Inst应用于（1）和恒等替换，得到 $\Gamma \vdash \mathrm{t}: \mathrm{T}$ （4）。将DM-GEN应用于（4），（2）和（3）得到 $\Gamma \vdash t: \forall x \bar{x} . T$，即 $\Gamma \vdash t: \forall X$。S。因此，DM-GEN'的效果可以通过DM-INST和DM-GEN获得。

显然，DM-INST是DM-INST'的一个特例，其中$\bar{Y}$为空。反之，考虑DM-INST'的一个实例，其前提是$\Gamma \vdash t$ : $\forall \overline{\mathrm{X}}$.T (1) 和 $\overline{\mathrm{Y}} \# \operatorname{ftv}(\forall \overline{\mathrm{X}}$. T) (2)。设$\rho$是一个重命名操作，它将$\overline{\mathrm{Y}}$与$\overline{\mathrm{Z}}$交换，其中$\overline{\mathrm{Z}} \# \operatorname{ftv}(\forall \overline{\mathrm{Y}} .[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T})$ (3) 和 $\overline{\mathrm{Z}} \# \operatorname{ftv}(\Gamma)$ (4)。将DM-InsT应用于(1)得到$\Gamma \vdash \mathrm{t}:[\overrightarrow{\mathrm{X}} \mapsto \rho \overrightarrow{\mathrm{T}}] \mathrm{T}$ (5)。将DM-GEN应用于(5)和(4)得到$\Gamma \vdash \mathrm{t}: \forall \overline{\mathrm{Z}} \cdot[\overrightarrow{\mathrm{X}} \mapsto \rho \overrightarrow{\mathrm{T}}] \mathrm{T}$，即$\Gamma \vdash \mathrm{t}: \forall \rho \overline{\mathrm{Y}} .[\overrightarrow{\mathrm{X}} \mapsto \rho \overrightarrow{\mathrm{T}}] \mathrm{T}$ (6)。现在，由(2)和(3)可知，$[\overrightarrow{\mathrm{X}} \mapsto \rho \overrightarrow{\mathrm{T}}] \mathrm{T}=\rho([\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T})$，所以(6)可以写成$\Gamma \vdash \mathrm{t}: \forall \rho \overline{\mathrm{Y}} . \rho([\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T})$，即$\Gamma \vdash \mathrm{t}: \rho(\forall \overline{\mathrm{Y}} .[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T})(7)$。由(3)，这正是$\Gamma \vdash \mathrm{t}: \forall \overrightarrow{\mathrm{Y}} \cdot[\overrightarrow{\mathrm{X}} \mapsto \overrightarrow{\mathrm{T}}] \mathrm{T}$。因此，DM-INST'的效果可以通过DM-INST和DM-GEN获得。

1.4.4 解决方案：让我们回忆一下，一个程序$t$是类型良好的当且仅当形如$C, \Gamma \vdash \mathrm{t}: \sigma$的判断成立，其中$C$是可以满足的。让我们证明，实际上可以不失一般性地要求$\sigma$是一个单型。

假设在 $\operatorname{HM}(X)$ 中可以推导出 $C, \Gamma \vdash \mathrm{t}: \sigma(\mathbf{1})$。让我们记 $\sigma=$ $\forall \overline{\mathrm{X}}[D].T$，其中 $\overline{\mathrm{X}} \# f t v(C)$（2）。将引理 1.4.1 应用于（1）得到 $C \Vdash$ $\exists \overline{\mathrm{X}} . D$（3）。根据 hm-Inst 规则，（1）意味着 $C \wedge D, \Gamma \vdash \mathrm{t}: \mathrm{T}$（4）。由（3），我们有 $C \equiv C \wedge \exists \overline{\mathrm{x}} . D \equiv \exists \overline{\mathrm{X}} .(C \wedge D)$。因为 $C$ 是可满足的，这意味着 $C \wedge D$ 也是可满足的。因此，涉及单型 $\mathrm{T}$ 的判断（4）证明了 $\mathrm{t}$ 是类型正确的。

我们已经证明了，一个程序$t$是类型良好的当且仅当形如$C, \Gamma \vdash \mathrm{t}: \mathrm{T}$的判断成立，其中$C$是可以满足的。因此，根据定理??和??，类型良好的性质对于两个规则集来说是相同的。

1.4.5 解：根据定理??，图1-8中的每一条规则在$\operatorname{HM}(X)$中都是可接受的。当然，HM-GEN也是如此。因此，通过图1-8的规则和$\mathrm{HM}-\mathrm{GEN}$可推导出的每一个判断都是有效的$\operatorname{HM}(X)$判断。

相反，假设在$\operatorname{HM}(X)$中成立$C, \Gamma \vdash \mathrm{t}: \sigma$ (1)。我们必须证明它是可以通过图1-8的规则和HM-GEN推导出来的。设我们写出$\sigma=$ $\forall \overline{\mathrm{x}}[D].T$，其中$\overline{\mathrm{x}} \# \mathrm{ftv}(C, \Gamma)$ (2)。通过HM-Inst和(1)，判断$C \wedge D, \Gamma \vdash \mathrm{t}: \mathrm{T}$ (3)在$\operatorname{HM}(X)$中成立。这个判断涉及到一个单型，所以根据定理??，它可以通过图1-8的规则推导出来。此外，从(3)和(2)，HM-GEN允许推导出$C \wedge \exists \sigma, \Gamma \vdash \mathrm{t}: \sigma$ (4)。将引理1.4.1应用于(1)得到$C \Vdash \exists \sigma$，因此判断(4)可以写成$C, \Gamma \vdash \mathrm{t}: \sigma$。我们已经证明了(1)可以通过图1-8的规则和HM-GEN推导出来。实际上，可以在推导的最后只应用一次HM-GEN。

1.5.1 解决方案：在类型系统 $\operatorname{PCB}(X)$ 中，我们有


![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-143.jpg?height=191&width=1114&top_left_y=1124&top_left_x=601)

类型变量 $z$ 在 VAR 的左侧实例中以自由变量的形式出现，并被泛化。然而，$\mathrm{z}_{2}$ 并没有接收到类型方案 $\forall \mathrm{Z} . \mathrm{Z}$，正如之前所暗示的那样，这是不健全的；相反，它接收到的是受限制的类型方案 $\forall z\left[z_{1} \preceq z\right] . z$。后者比前者更具限制性：实际上，前者声称 $z_{2}$ 具有每种类型，而后者仅声称对 $z_{1}$有效的每种类型也对 $z_{2}$ 有效。现在让我们检查一下派生树的根处出现的约束 let $z_{1}$ : $\mathrm{X} ; \mathrm{z}_{2}: \forall \mathrm{Z}\left[\mathrm{z}_{1} \preceq \mathrm{Z}\right] . \mathrm{Z}$ in $\mathrm{z}_{2} \preceq \mathrm{Y}$。通过 C-INID 和 C-IN*，它等价于 let $\mathrm{z}_{1}: \mathrm{X}$ in $\exists \mathrm{Z} .\left(\mathrm{z}_{1} \preceq \mathrm{Z} \wedge \mathrm{Z} \leq \mathrm{Y}\right)$ 以及 $\exists \mathrm{Z}$. $\mathrm{X} \leq \mathrm{Z} \wedge \mathrm{Z} \leq \mathrm{Y}$)，这通过 $\mathrm{C}$-ExTRans 等价于 $\mathrm{X} \leq \mathrm{Y}$。因此，上述派生树的根处的判断可以写成 $\mathrm{X} \leq$ $\mathrm{Y} \vdash \lambda \mathrm{z}_{1}$. let $\mathrm{z}_{2}=\mathrm{z}_{1}$ in $\mathrm{z}_{2}: \mathrm{X} \rightarrow \mathrm{Y}$。换句话说，表达式 let $\mathrm{z}_{2}=$ $\mathrm{z}_{1}$ in $\mathrm{z}_{2}$ 只有在假设 $\mathrm{X}$ 是 $\mathrm{Y}$ 的子类型的情况下才具有类型 $\mathrm{X} \rightarrow \mathrm{Y}$，这是健全的。尽管 LET 允许类型变量的无限制泛化，但它仍然健全，因为它产生的类型方案通常具有自由程序标识符，如上面提到的 $\forall \mathrm{Z}\left[\mathbf{z}_{1} \preceq \mathrm{Z}\right] . \mathrm{Z}$。

1.7.10 解法：令 $\mathcal{E}=$ 令 $\mathrm{z}=\mathcal{E}_{1}$ 在 $\mathrm{t}_{1}$ 中，且 $\mathcal{E}_{1}[\mathrm{t}] / \mu \sqsubseteq \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}$ (1)。那么，

$$
\begin{align*}
& \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket \mathcal{E}[\mathrm{t}] / \mu: \mathrm{T} / M \rrbracket \\
= & \text { let } \Gamma_{0} ; \operatorname{ref} M \text { in }\left(\left(\text { let } \mathrm{z}: \forall \mathrm{x}\left[\llbracket \mathcal{E}_{1}[\mathrm{t}]: \mathrm{x} \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket\right) \wedge \llbracket \mu: M \rrbracket\right)  \tag{2}\\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M ; \mathrm{z}: \forall \mathrm{x}\left[\llbracket \mathcal{E}_{1}[\mathrm{t}] / \mu: \mathrm{X} / M \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket  \tag{3}\\
\equiv & \text { let } \Gamma_{0} ; \operatorname{ref} M ; \mathrm{z}: \forall \mathrm{x}\left[\text { let } \Gamma_{0} ; \operatorname{ref} M \text { in } \llbracket \mathcal{E}_{1}[\mathrm{t}] / \mu: \mathrm{x} / M \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket  \tag{4}\\
\Vdash & \text { let } \Gamma_{0} ; \operatorname{ref} M ; \mathrm{z}: \forall \mathrm{x} \overline{\mathrm{Y}}\left[\text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}: \mathrm{x} / M^{\prime} \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket \tag{5}
\end{align*}
$$

其中（2）是根据约束生成的定义，其中 $\mathrm{X} \notin \operatorname{ftv}(\mathrm{T}, M)(\mathbf{6})$；（3）是根据（6）、C-LETAND 和约束生成的定义；（4）是根据（6）和C-LetDup；（5）是根据（1）和C-LETEx得出的，对于某些 $\overline{\mathrm{Y}}$ 和 $M^{\prime}$，使得 $\overline{\mathrm{Y}} \# \operatorname{ftv}(\mathrm{X}, M)(\mathbf{7})$ 和 $f t v\left(M^{\prime}\right) \subseteq \overline{\mathrm{Y}} \cup f t v(M)$ （8）以及 $\operatorname{dom}\left(M^{\prime}\right)=\operatorname{dom}\left(\mu^{\prime}\right)$ 且 $M^{\prime}$ 扩展了 $M$。注意（6）、（7）和（8）意味着 $\mathrm{X} \notin f t v\left(M^{\prime}\right)$ （9）。

在这一点上，决定新分配存储单元类型的类型变量 $\overline{\mathrm{Y}}$ 在分配给 $z$ 的类型方案中被普遍量化，这是我们不希望看到的。我们陷入了困境，因为通常我们不能将 C-LETALL 应用于将 $\exists \bar{Y}$ 从 let 约束中提取出来。现在，让我们假设通过某些外部手段，我们得到了保证 $\overline{\mathrm{Y}}=\varnothing \mathbf{( 1 0 )}$。那么，我们可以按如下方式进行：

$$
\begin{align*}
& \equiv \text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} ; \mathrm{z}: \forall \mathrm{X}\left[\text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket \mathcal{E}_{1}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}: \mathrm{X} / M^{\prime} \rrbracket\right] . \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket  \tag{11}\\
& \equiv \text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket \mathcal{E}\left[\mathrm{t}^{\prime}\right] / \mu^{\prime}: \mathrm{T} / M^{\prime} \rrbracket \tag{12}
\end{align*}
$$

(11) 是由出现在 $\llbracket \mathrm{t}_{1}: \mathrm{T} \rrbracket$ 中看似空闲的内存位置是 $\operatorname{dom}(\mu)$ 的成员这一事实得出的，因此它们不是 $\operatorname{dom}\left(M^{\prime}\right) \backslash \operatorname{dom}(M)$ 的成员；(12) 是通过逆向执行导致 (4) 的步骤得到的。

要求 $\overline{\mathrm{Y}}$ 为空，即 $f t v(M)=f t v\left(M^{\prime}\right)$，这是经典的（Tofte, 1988）。这是如何实施的？假设每个 let 构造的左侧必须是一个非扩展表达式。根据假设（ii）和（iii），这个不变量通过归约得到保持。所以，$\mathcal{E}_{1}[t]$ 必须是非扩展的，根据假设（i），这保证了归约步骤不会分配新的内存单元。那么，$\mu^{\prime}$ 就是 $\mu$，所以 $M^{\prime}$ 就是 $M$。

1.9.1 解决方案：我们首先必须确保 R-AdD 遵守 $\sqsubseteq$ （定义1.7.5）。由于规则是纯的，只需建立让 $\Gamma_{0}$ 在 $\llbracket \hat{k}_{1} \hat{+} \hat{k}_{2}: \mathrm{T} \rrbracket$ 中蕴含让 $\Gamma_{0}$ 在 $\llbracket \widehat{k_{1}+k_{2}}: \mathrm{T} \rrbracket$ 中即可。实际上，我们有以下结果：

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

其中（1）是根据约束生成的定义；（2）是根据 $\Gamma_{0}$ 的定义，通过C-INID和C-IN*；（3）是通过C-ARRow和子类型反对称性。

(4)是由C-ExAnd和C-NAmE确定的；(5)再次根据$\Gamma_{0}$的定义，通过C-InId和$\mathrm{C}-\mathrm{IN}^{*}$，以及约束生成的定义得出。

其次，我们必须检查配置 $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$（其中 $k \geq 0$ ）是否有良好的类型，那么它要么是可约的，要么 $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k}$ 是一个值。

我们首先检查每个类型为int的良类型值是否具有形式$\hat{k}$。确实，假设$\Gamma_{0} ; \operatorname{ref} M$在$\llbracket \mathrm{v}:$ int $\rrbracket$中是可满足的。那么，$v$不能是一个程序变量，因为良类型值必须是闭合的。$v$不能是一个内存位置$m$，否则ref $M(m) \leq$ int将是可满足的——但类型构造器ref和int是不兼容的。$v$不能是$\hat{+}$或$\hat{+} \mathrm{v}^{\prime}$，否则int $\rightarrow$ int $\rightarrow$ int $\leq$ int或int $\rightarrow$ int $\leq$ int将是可满足的——但类型构造器$\rightarrow$和int是不兼容的。同样，$\mathrm{v}$不能是一个$\lambda$-抽象。因此，$\mathrm{v}$必须具有形式$\hat{k}$，因为这是唯一剩下的情况。

接下来，我们注意到，根据约束生成规则，如果配置 $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$ 是类型正确的，那么形如 let $\Gamma_{0}$; ref $M$ in $\left(\mathrm{c} \preceq \mathrm{x}_{1} \rightarrow \ldots \rightarrow \mathrm{x}_{k} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}_{1}: \mathrm{x}_{1} \rrbracket \wedge \ldots \wedge \llbracket \mathrm{v}_{k}: \mathrm{x}_{k} \rrbracket\right)$ 的约束是可以满足的。我们现在根据 $c$ 的不同情况进行推理。

- 情况 $\mathrm{c}$ 是 $\hat{k}$。那么，$\Gamma_{0}(\mathrm{c})$ 是 int。因为类型构造器 int 和 $\rightarrow$ 互不兼容，这意味着 $k=0$。由于 $\hat{k}$ 是一个构造器，表达式是一个值。
- 情况 $\mathrm{c}$ 是 $\hat{+}$。我们可以假设 $k \geq 2$，因为否则表达式是一个值。那么，$\Gamma_{0}(\mathrm{c})$ 是 int $\rightarrow$ int $\rightarrow$ int，因此，根据 C-Arrow 规则，上述约束蕴含了 let $\Gamma_{0} ; \operatorname{ref} M$ in $\left(\mathrm{x}_{1} \leq \operatorname{int} \wedge \mathrm{X}_{2} \leq \operatorname{int} \wedge \llbracket \mathrm{v}_{1}: \mathrm{X}_{1} \rrbracket \wedge \llbracket \mathrm{v}_{2}: \mathrm{X}_{2} \rrbracket\right)$，这通过引理 1.6.3，意味着 let $\Gamma_{0} ; \operatorname{ref} M$ in $\left(\llbracket \mathrm{v}_{1}: \operatorname{int} \rrbracket \wedge \llbracket \mathrm{v}_{2}: \operatorname{int} \rrbracket\right)$。因此，$\mathrm{v}_{1}$ 和 $\mathrm{v}_{2}$ 都是类型为 int 的字面量 $\hat{k}_{1}$ 和 $\hat{k}_{2}$。因此，这个配置是可以通过 R-ADD 还原的。

1.9.5 解决方案：我们首先必须确保 R-Ref、R-Deref 和 R-Assign 遵守 $\sqsubseteq($ 定义1.7.5)。

- 案例R-REF。减缩是 ref v/ $\varnothing \longrightarrow m /(m \mapsto \mathrm{v})$，其中 $m \notin$ fpi(v) (1)。令 $\mathrm{T}$ 为任意类型。根据定义1.7.5，目标是证明存在一组类型变量 $\overline{\mathrm{Y}}$ 和一个存储类型 $M^{\prime}$ 使得 $\overline{\mathrm{Y}} \# \operatorname{ftv}(\mathrm{T})$ 且 $f t v\left(M^{\prime}\right) \subseteq \overline{\mathrm{Y}}$ 并且 $\operatorname{dom}\left(M^{\prime}\right)=\{m\}$，并且令 $\Gamma_{0}$ 在 $\llbracket$ ref $\mathrm{v}: \mathrm{T} \rrbracket$
蕴含 $\exists \overline{\mathrm{Y}}$。令 $\Gamma_{0}$; ref $M^{\prime}$ 在 $\llbracket m /(m \mapsto \mathrm{v}): \mathrm{T} / M^{\prime} \rrbracket$。现在，我们有


$$
\begin{align*}
& \text { let } \Gamma_{0} \text { in } \llbracket \operatorname{ref} \mathrm{v}: \mathrm{T} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XY} .(\mathrm{Y} \rightarrow \operatorname{ref} \mathrm{Y} \leq \mathrm{X} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}: \mathrm{X} \rrbracket)  \tag{2}\\
\equiv & \exists \mathrm{Y} . \text { let } \Gamma_{0} \text { in }(\operatorname{ref} \mathrm{Y} \leq \mathrm{T} \wedge \llbracket \mathrm{v}: \mathrm{Y} \rrbracket)  \tag{3}\\
\equiv & \exists \mathrm{Y} . \text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in }\left(m \preceq \mathrm{T} \wedge \llbracket \mathrm{v}: M^{\prime}(m) \rrbracket\right)  \tag{4}\\
\equiv & \exists \mathrm{Y} . \text { let } \Gamma_{0} ; \operatorname{ref} M^{\prime} \text { in } \llbracket m /(m \mapsto \mathrm{v}): \mathrm{T} / M^{\prime} \rrbracket \tag{5}
\end{align*}
$$

其中（2）是根据约束生成的定义以及 $\Gamma_{0}(\mathrm{ref})$ 的定义；（3）是根据C-Arrow，引理1.6.4，以及C-InEx；（4）假设 $M^{\prime}$ 定义为 $m \mapsto \mathrm{Y}$，并且由（1），C-INID和C-IN*得出；而（5）则是根据约束生成的定义。

子情况 R-DEREF。减缩为 $! m /(m \mapsto \mathrm{v}) \longrightarrow \mathrm{v} /(m \mapsto \mathrm{v})$。设 $\mathrm{T}$ 为任意类型，且设 $M$ 为域 $\{m\}$ 的存储类型。我们有

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

其中（1）是根据约束生成定义以及根据 $\Gamma_{0}(!)$ 的定义；（2）是根据C-Arrow和C-InId；（3）是由C-ExTrans以及ref是一个不变类型构造器这一事实得出；（4）是根据C-NAMEEQ；（5）是根据引理1.6.3和C-DuP；而（6）再次根据约束生成的定义得出。

案例 R-分配。约简是 $m:=\mathrm{v} /\left(m \mapsto \mathrm{v}_{0}\right) \longrightarrow \mathrm{v} /(m \mapsto \mathrm{v})$。令 $\mathrm{T}$ 为任意类型，令 $M$ 为域 $\{m\}$ 的存储类型。我们有

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

其中（1）和（2）是根据约束生成的定义；（3）是根据CArrow和C-InId；（4）是根据C-ExTrans、引理1.6.4以及ref是一个不变类型构造器的事实；（5）是根据C-NAMEEQ；而（6）则是从前一个案例中获得的。

其次，我们必须检查配置 $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$（其中 $k \geq 0$）是否类型正确，如果是，那么它要么是可约的，要么 $\mathrm{c} \mathrm{v}_{1} \ldots \mathrm{v}_{k}$ 是一个值。这里我们只给出了这个证明的概要；具体证明细节可参见练习1.9.1的解答，那里有一个类似证明的详细说明。

我们首先检查每个类型为 ref $\mathrm{T}$ 的良好类型的值是否都是一个内存位置。这个断言依赖于这样一个事实：类型构造器 ref 是孤立的。

接下来，我们注意到，根据约束生成规则，如果配置 $\mathrm{c}_{1} \ldots \mathrm{v}_{k} / \mu$ 是良好类型的，那么形如 let $\Gamma_{0}$; ref $M$ in $\left(\mathrm{c} \preceq \mathrm{x}_{1} \rightarrow \ldots \rightarrow \mathrm{x}_{k} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}_{1}: \mathrm{x}_{1} \rrbracket \wedge \ldots \wedge \llbracket \mathrm{v}_{k}: \mathrm{x}_{k} \rrbracket\right)$ 的约束是可以满足的。我们现在通过$\mathrm{c}$的案例来进行推理。

- 情况c是引用。如果$k=0$，则表达式是一个值；否则，它可以被$\mathrm{R}$-REF简化。
- 情况c是!。我们可以假设$k \geq 1$，因为否则表达式是一个值。根据$\Gamma_{0}(!)$的定义，上述约束蕴含了 let $\Gamma_{0} ; \operatorname{ref} M$ in $\exists \mathrm{Y}$。(ref $\left.\mathrm{Y} \rightarrow \mathrm{Y} \leq \mathrm{X}_{1} \rightarrow \ldots \rightarrow \mathrm{X}_{k} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}_{1}: \mathrm{X}_{1} \rrbracket\right)$，由C-Arrow，引理1.6.3，和C-INEx，蕴含了$\exists \mathrm{Y}$.let $\Gamma_{0} ; \operatorname{ref} M$ in $\llbracket \mathrm{v}_{1}: \operatorname{ref} \mathrm{Y} \rrbracket$。因此，$\mathrm{v}_{1}$是一个类型为ref $\mathrm{Y}$的好类型变量。根据上述备注，$\mathrm{v}_{1}$必须是一个内存位置$m$。此外，因为每个类型良好的配置都是闭合的，$m$必须是$\operatorname{dom}(\mu)$的一个成员。结果是，配置 ref $\mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$ 可以被R-DEREF简化。
- 情况c是$:=$。我们可以假设$k \geq 2$，因为否则表达式是一个值。如上所述，我们检查$v_{1}$必须是一个内存位置，并且是$\operatorname{dom}(\mu)$的成员。因此，配置可以被R-Assign简化。

1.9.6 解法：我们首先必须确保R-Fix尊重$\sqsubseteq$（定义1.7.5）。由于规则是纯的，只需证明让$\Gamma_{0}$在$\llbracket f i x v_{1} v_{2}: T \rrbracket$中蕴含着让$\Gamma_{0}$在$\llbracket \mathrm{v}_{1}(f i x v_{1}) \mathrm{v}_{2}: \mathrm{T} \rrbracket$中即可。设$C$表示约束fix $\preceq$ $((\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow(\mathrm{X} \rightarrow \mathrm{Y})) \rightarrow \mathrm{X} \rightarrow \mathrm{Y} \wedge \mathrm{Y} \leq \mathrm{T} \wedge \llbracket \mathrm{v}_{1}:(\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow(\mathrm{X} \rightarrow \mathrm{Y}) \rrbracket \wedge \llbracket \mathrm{v}_{2}: \mathrm{X} \rrbracket$。我们有

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

其中（1）是由约束生成的定义；（2）是由 $\Gamma_{0}(f i x)$ 的定义；（3）是由C-ARrow和引理1.6.4；（4）是由 $\Gamma_{0}(f i x)$ 的定义。根据定理1.6.2和WEAKEn，判断 $C \vdash \mathrm{v}_{1}:(\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow (\mathrm{X} \rightarrow \mathrm{Y})$ 和 $C \vdash \mathrm{v}_{2}: \mathrm{X}$ 成立。根据Var，Weaken，App和Sub规则，可以得出 $C \vdash \mathrm{v}_{1}\left(f i x v_{1}\right) v_{2}: \mathrm{T}$ 成立。根据定理1.6.6，这意味着 $C \Vdash \llbracket \mathrm{v}_{1}\left(f i x \mathrm{v}_{1}\right) \mathrm{v}_{2}: \mathrm{T} \rrbracket$ 成立。根据蕴含的相等性和C-Ex*，（4）意味着在 $\llbracket v_{1}\left(f i x v_{1}\right) v_{2}: T \rrbracket$ 中让 $\Gamma_{0}$ 成立。

其次，我们必须检查配置 $f i x v_{1} \ldots v_{k} / \mu$（其中 $k \geq 0$）是否类型正确，如果是，那么它要么是可约的，要么 $f i x v_{1} \ldots v_{k}$ 是一个值。这是显然的，因为当 $k<2$ 时它是一个值，而当 $k \geq 2$ 时它可以通过 R-FIX 规则被约简。

我们现在回忆起，ML编程语言提供的letrec构造$f=\lambda$ z.t $_{1}$ 在 $t_{2}$ 可以被视为语法糖，等价于 let $\mathrm{f}=$ fix $\left(\lambda f . \lambda z . t_{1}\right)$ 在 $t_{2}$，并着手发现由这种定义产生的约束生成规则。我们有

$$
\begin{align*}
& \text { let } \Gamma_{0} \text { in } \llbracket \mathrm{fix}\left(\lambda \mathrm{f} . \lambda \mathrm{z} . \mathrm{t}_{1}\right): \mathrm{T} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{Z} .\left(\mathrm{fix} \preceq \mathrm{Z} \rightarrow \mathrm{T} \wedge \llbracket \lambda \mathrm{f} . \lambda \mathrm{z} \cdot \mathrm{t}_{1}: \mathrm{Z} \rrbracket\right)  \tag{1}\\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XY} .\left(\mathrm{X} \rightarrow \mathrm{Y} \leq \mathrm{T} \wedge \llbracket \lambda f \mathrm{f} . \lambda \mathrm{z} . \mathrm{t}_{1}:(\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow(\mathrm{X} \rightarrow \mathrm{Y}) \rrbracket\right)  \tag{2}\\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{XY} .\left(\mathrm{X} \rightarrow \mathrm{Y} \leq \mathrm{T} \wedge \text { let } \mathrm{f}: \mathrm{X} \rightarrow \mathrm{Y} ; \mathrm{z}: \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{Y} \rrbracket\right) \tag{3}
\end{align*}
$$

其中（1）是根据约束生成的定义；（2）是根据 $\Gamma_{0}$ （固定）的定义、C-ARrow规则以及引理1.6.4；（3）源自引理1.6.5。这使我们能够写出以下内容：

$$
\begin{aligned}
& \text { let } \Gamma_{0} \text { in } \llbracket \text { let } f=f i x\left(\lambda f . \lambda z . t_{1}\right) \text { in } t_{2}: T \rrbracket \\
& \equiv \text { let } \Gamma_{0} ; f: \forall \mathrm{z}\left[\llbracket \mathrm{fix}\left(\lambda \mathrm{f} \cdot \lambda \mathrm{z} \cdot \mathrm{t}_{1}\right): \mathrm{z} \rrbracket\right] . \mathrm{z} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket \\
& \equiv \text { let } \Gamma_{0} ; f: \forall \mathrm{Z}\left[\exists \mathrm{XY} .\left(\mathrm{X} \rightarrow \mathrm{Y} \leq \mathrm{Z} \wedge \text { let } \mathrm{f}: \mathrm{X} \rightarrow \mathrm{Y} ; \mathrm{z}: \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{Y} \rrbracket\right)\right] . \mathrm{Z} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket \\
& \equiv \text { let } \Gamma_{0} ; f: \forall \mathrm{XY}\left[\text { let } \mathrm{f}: \mathrm{X} \rightarrow \mathrm{Y} ; \mathrm{z}: \mathrm{X} \text { in } \llbracket \mathrm{t}_{1}: \mathrm{Y} \rrbracket\right] . \mathrm{X} \rightarrow \mathrm{Y} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket
\end{aligned}
$$

其中（4）是根据约束生成的定义；（5）来自C-LETDuP和之前的等价系列；（6）是根据C-LETEx，C-ExTrans和引理1.3.22。

1.9.21 解决方案：我们有

$$
\begin{align*}
& \text { } \text { match }_{1} \text { with } z \cdot \mathrm{t}_{2}: \mathrm{T} \rrbracket \\
\equiv & \text { let } \forall \mathrm{xX^{ \prime }}\left[\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket \wedge \text { let } \mathrm{z}: \mathrm{X}^{\prime} \text { in } \llbracket \mathrm{X}: \mathrm{z} \rrbracket\right] \cdot\left(\mathrm{z}: \mathrm{X}^{\prime}\right) \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket  \tag{1}\\
\equiv & \text { let } \mathrm{z}: \forall \mathrm{X}^{\prime}\left[\exists \mathrm{X} \cdot\left(\llbracket \mathrm{t}_{1}: \mathrm{x} \rrbracket \wedge \mathrm{X} \leq \mathrm{X}^{\prime}\right)\right] \cdot \mathrm{X}^{\prime} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket  \tag{2}\\
\equiv & \text { let } \mathrm{z}: \forall \mathrm{X}^{\prime}\left[\llbracket \mathrm{t}_{1}: \mathrm{X}^{\prime} \rrbracket\right] \cdot \mathrm{X}^{\prime} \text { in } \llbracket \mathrm{t}_{2}: \mathrm{T} \rrbracket  \tag{3}\\
\equiv & \llbracket \text { let } \mathrm{z}=\mathrm{t}_{1} \text { in } \mathrm{t}_{2}: \mathrm{T} \rrbracket \tag{4}
\end{align*}
$$

其中（1）是根据匹配的约束生成的定义；（2）是根据模式约束生成的定义，通过C-InID，C-IN*和C-LETEx；（3）是根据引理1.6.4；（4）是根据let的约束生成的定义。

1.9.26 解：类型方案 $\forall \overline{\mathrm{X}} . \mathrm{T} \rightarrow \mathrm{T}$ 可以写成 $\forall \overline{\mathrm{X}}$. $[\mathrm{X} \mapsto \mathrm{T}](\mathrm{X} \rightarrow \mathrm{X})$。此外，$\overline{\mathrm{X}} \# \forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$ 成立。因此，$\forall \overline{\mathrm{X}} . \mathrm{T} \rightarrow \mathrm{T}$ 是 $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$ 在DM-INST'意义上的一个实例。由于DM-INST'是类型系统DM的一个可允许规则，并且显然恒等函数 $\lambda z . z$ 具有类型 $\forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}$，它也必须有类型 $\forall \overline{\mathrm{X}} . \mathrm{T} \rightarrow \mathrm{T}$。（这一事实的直接证明并不困难。）所以，析构器 $(\cdot: \exists \overline{\mathrm{X}} . \mathrm{T})$ 不仅具有恒等语义，还具有恒等类型。这表明我们的定义是健全的。

让我们现在来检查定义1.7.6中的要求(i)。由于R-注释是纯的，因此只需证明在$\llbracket(\mathrm{v}: \exists \overline{\mathrm{X}} . \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$中的let $\Gamma_{0}$蕴含了在$\llbracket \mathrm{v}: \mathrm{T}^{\prime} \rrbracket$中的let $\Gamma_{0}$即可。

Now, we have

$$
\begin{array}{ll} 
& \text { let } \Gamma_{0} \text { in } \llbracket(\mathrm{v}: \exists \overline{\mathrm{X}} . \mathrm{T}): \mathrm{T}^{\prime} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{X} \overline{\mathrm{X}} \cdot\left(\mathrm{T} \rightarrow \mathrm{T} \leq \mathrm{X} \rightarrow \mathrm{T}^{\prime} \wedge \llbracket \mathrm{v}: \mathrm{X} \rrbracket\right) \\
\equiv & \text { let } \Gamma_{0} \text { in } \exists \mathrm{X} \overline{\mathrm{X}} \cdot\left(\mathrm{X} \leq \mathrm{T} \leq \mathrm{T}^{\prime} \wedge \llbracket \mathrm{v}: \mathrm{X} \rrbracket\right) \\
\Vdash & \text { let } \Gamma_{0} \text { in } \llbracket \mathrm{v}: \mathrm{T}^{\prime} \rrbracket \tag{3}
\end{array}
$$

其中（1）是根据约束生成的定义以及根据 $\Gamma_{0}((\cdot$ : $\exists \overline{\mathrm{X}} . \mathrm{T})$ ) 的定义；（2）是根据C-ArRow；（3）是根据引理1.6.3和C-EX*得出的。

1.10.5 解决方案：我们有

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

其中（1）是根据通用类型注释的约束生成定义；（2）是通过将 $\exists \mathrm{Z}$ 的作用域限制在第二个连词上，然后完全删除后者，因为它等价于真，根据引理1.6.5；（3）是根据约束生成的定义，根据 $\Gamma_{0}(\hat{+})$ 和 $\Gamma_{0}(\hat{1})$ 的定义，以及一些简单的等价法则；（4）来自C-ARrow和子类型的反对称性；（5）来自这样一个事实，即int和（比如说）int $\rightarrow$ int具有不同的解释，因为类型构造器int和$\rightarrow$是不兼容的。另一方面，我们有：

$$
\begin{align*}
& \text { let } \Gamma_{0} \text { in } \exists \mathrm{Z} \cdot \llbracket(\lambda \mathrm{z} \cdot \mathrm{z}: \forall \mathrm{X} . \mathrm{X} \rightarrow \mathrm{X}): \mathrm{Z} \rrbracket \\
\equiv & \text { let } \Gamma_{0} \text { in } \forall \mathrm{X} . \text { let } \mathrm{z}: \mathrm{X} \text { in } \llbracket \mathrm{z}: \mathrm{X} \rrbracket  \tag{1}\\
\equiv & \forall \mathrm{X} .(\mathrm{X} \leq \mathrm{X})  \tag{2}\\
\equiv & \text { true } \tag{3}
\end{align*}
$$

其中（1）如上所述获得；（2）根据约束生成的定义，C-InID 和 C-IN*；（3）是由子类型的反射性得出。

1.10.6 解决方案：在通用类型变量引入的朴素约束生成规则下，约束 $\llbracket \forall \mathrm{X} .(\lambda \mathrm{z} \cdot \mathrm{z}: \mathrm{X} \rightarrow \mathrm{X}): \mathrm{Z} \rrbracket$ 等价于 $\forall \mathrm{X} .(\llbracket \lambda z . z: X \rightarrow X \rrbracket \wedge \mathrm{X} \rightarrow \mathrm{X} \leq \mathrm{Z})$。由于第一个合取项是重言式，这进而等价于 $\forall \mathrm{X}$. $(\mathrm{X} \rightarrow \mathrm{X} \leq \mathrm{Z}$)。在一个非退化的自由项模型中，如果子类型被解释为等价，这个约束是不可满足的。在一个配备了最小类型 $\perp$ 和最大类型 $\top$ 的非结构化子类型模型中，它等价于 $\perp \rightarrow \top \leq \mathrm{Z}$。这是一个相当限制性的约束：由于没有任何值具有类型 $\perp$，类型为（$\perp \rightarrow T$ 的超类型）的函数在运行时永远不能被调用。这种情况明显是不满意的。检查 $\forall \mathrm{X} . \llbracket \lambda z . z: \mathrm{X} \rightarrow \mathrm{X} \rrbracket$ 是否成立确实是我们意图的一部分，但让 $\mathrm{Z}$ 成为每个 $\mathrm{X}$ 的 $\mathrm{X} \rightarrow \mathrm{X}$ 的超类型并不是。

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-150.jpg?height=56&width=1312&top_left_y=732&top_left_x=418)
$\overline{\mathrm{X}} \# \mathrm{ftv}\left(\mathrm{T}^{\prime}\right)$ (3). By (1), (2), (3), and by definition of constraint generation for local universal type annotations, $\llbracket(t: \forall \overline{\mathrm{X}} . \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ is well-defined and is $\forall \overline{\mathrm{X}} . \llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \exists \overline{\mathrm{X}} .\left(\mathrm{T} \leq \mathrm{T}^{\prime}\right)$ (4). By (3) and by definition of constraint generation for introduction of universal type variables and for general type annotations, $\llbracket \forall \overline{\mathrm{X}} .(\mathrm{t}: \mathrm{T}): \mathrm{T}^{\prime} \rrbracket$ is $\forall \overline{\mathrm{X}} \cdot \exists \mathrm{Z} .(\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{Z}) \wedge \exists \overline{\mathrm{X}} .\left(\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{T}^{\prime}\right)$, where $\mathrm{Z}$ is fresh, which we may immediately simplify to $\forall \overline{\mathrm{X}}$ $\llbracket \mathrm{t}: \mathrm{T} \rrbracket \wedge \exists \overline{\mathrm{X}}$. $\left(\llbracket t: \mathrm{T} \rrbracket \wedge \mathrm{T} \leq \mathrm{T}^{\prime}\right)$ (5). Using C-ExAnd and Lemma 1.10.1, it is straightforward to check that (4) and (5) are equivalent.

1.10.9 解决方案：我们有

$$
\begin{array}{ll} 
& \exists \mathrm{Z} \cdot \llbracket \lambda \mathrm{z} \cdot \forall \mathrm{X} \cdot(\mathrm{z}: \mathrm{x}): \mathrm{z \rrbracket} \\
\Vdash & \exists \mathrm{Z}_{1} \mathrm{Z}_{2} \cdot \text { let } \mathrm{z}: \mathrm{Z}_{1} \text { in } \llbracket \forall \mathrm{X} .(\mathrm{z}: \mathrm{x}): \mathrm{Z}_{2} \rrbracket \\
\text { IF } & \exists \mathrm{Z}_{1} \cdot \forall \mathrm{X} \cdot\left(\mathrm{Z}_{1} \leq \mathrm{X}\right) \tag{2}
\end{array}
$$

(1) 是根据 λ-抽象的约束生成定义，丢弃了与 Z, Z1 和 Z2 相关的约束；(2) 是根据普遍类型变量引入的约束生成定义，这次丢弃了关于 Z2 的信息。现在，在一个非退化等价模型中，约束(2)等价于假。实际上，为了使(2)可满足，子类型的解释必须承认一个最小元素 ⊥。我们现在看到，[λz.∀X.(z:X):Z] 是一个非常严格的约束。事实上，它要求 z 同时具有所有类型。因为 z 是 λ-绑定——因此是单态的——它实际上必须具有类型 ⊥。另一方面，我们有

$$
\begin{align*}
& \exists \mathrm{Z} \cdot \llbracket \forall \mathrm{X} \cdot \lambda \mathrm{z} \cdot(\mathrm{z}: \mathrm{X}): \mathrm{Z} \rrbracket \\
\equiv & \forall \mathrm{x} \cdot \exists \mathrm{Z} \cdot \llbracket \lambda \mathrm{z} \cdot(\mathrm{z}: \mathrm{x}): \mathrm{Z} \rrbracket  \tag{1}\\
\equiv & \forall \mathrm{X} \cdot \exists \mathrm{ZZ} \mathrm{Z}_{1} \cdot\left(\mathrm{Z}_{2} \leq \mathrm{X} \wedge \mathrm{X} \leq \mathrm{Z}_{2} \wedge \mathrm{Z}_{1} \rightarrow \mathrm{Z}_{2} \leq \mathrm{Z}\right)  \tag{2}\\
\equiv & \text { true } \tag{3}
\end{align*}
$$

其中（1）是根据通用类型变量引入的约束生成的定义，省略了第二个连结，它是由第一个连结所蕴含的；（2）是根据引理1.6.5，通用类型注解的约束生成的定义，以及一些简单的等价律；（3）遵循C-NAMEEQ和见证替换 $\left[\mathrm{Z}_{1} \mapsto \mathrm{X}, \mathrm{Z}_{2} \mapsto \mathrm{X}, \mathrm{Z} \mapsto(\mathrm{X} \rightarrow \mathrm{X})\right]$。

![](https://cdn.mathpix.com/cropped/2024_03_11_24264b834bbd98369519g-151.jpg?height=43&width=484&top_left_y=545&top_left_x=758)

$$
\begin{aligned}
& \equiv \text { let } f: \forall x\left[\llbracket f i x f: S . \lambda z . t_{1}: x \rrbracket\right] . x \text { in } \llbracket t_{2}: T \rrbracket \\
& \equiv \text { let } f: \forall X\left[\text { let } f: S \text { in } \llbracket \lambda z . t_{1}: S \rrbracket \wedge S \preceq X\right] . X \text { in } \llbracket t_{2}: T \rrbracket \\
& \equiv \text { let } f: S \text { in } \llbracket \lambda z . t_{1}: S \rrbracket \wedge \text { let } f: \forall x[S \preceq x] . x \text { in } \llbracket t_{2}: T \rrbracket \\
& \equiv \text { let } f: S \text { in }\left(\llbracket \lambda z \cdot t_{1}: S \rrbracket \wedge \llbracket t_{2}: T \rrbracket\right)
\end{aligned}
$$

其中（1）是根据letrec语法糖的定义以及let结构约束生成的定义；我们有 $\mathrm{X} \notin f t v\left(\mathrm{~S}, \mathrm{t}_{1}\right)$；（2）是根据fix的约束生成定义；（3）是根据C-LETAND；（4）是由类型方案$\forall \mathrm{X}[\mathrm{S} \preceq \mathrm{X}] . \mathrm{X}$与$\mathrm{S}$之间的等价性推导出来的——这本身是C-ExTRAns的直接结果——以及C-InAnd。

1.11.16 解决方案：我们同时在子类型模型和平等唯一模型中推理，也就是说，我们只依赖在两种模型中都有效的属性。

我们必须首先确保规则RD-DEFAULT、RD-Found和RD-Follow遵守（定义1.7.5）。

- 案例RD-默认。减化是 $\{\mathrm{v}\} .\{\ell\} \xrightarrow{\delta} \mathrm{v}$，这是纯粹的。因此，只需证明让 $\Gamma_{0}$ 在 $\llbracket\{\mathrm{v}\} \cdot\{\ell\}: \mathrm{T} \rrbracket$ 中蕴含着让 $\Gamma_{0}$ 在 $\llbracket \mathrm{v}: \mathrm{T} \rrbracket$ 中即可。实际上，我们有：

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

其中（1）是根据约束生成的定义；（2）是根据 $\Gamma_{0}$, C-InId 的定义；（3）根据 $\Pi, \ell$ 以及 $\rightarrow$ 的变化，C-And, C-Ex*, C-ExAnd；（4）根据 C-Row-DL 和 $\ell$ 的协方差；（5）根据引理1.6.3。

案例 RD-发现：减少是 $\{\mathrm{w}$ 与 $\ell=\mathrm{v}\} .\{\ell\} \xrightarrow{\delta} \mathrm{v}$. 只需建立让 $\Gamma_{0}$ 在 $\llbracket\{\mathrm{w}$ 与 $\ell=\mathrm{v}\} \cdot\{\ell\}: \mathrm{T} \rrbracket$ 中蕴含让 $\Gamma_{0}$ 在 $\llbracket \mathrm{v}: \mathrm{T} \rrbracket$ 中。实际上，我们有：

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

其中（1）是根据约束生成的定义；（2）是根据 $\Gamma_{0}$, C-InID 的定义；（3）根据 $\Pi, \ell$, 以及 $\rightarrow$ 的方差，C-And, C-Ex*, C-ExAnd；（4）根据引理1.6.3。

- 案例RD-跟进 证据与上一个案例相似。

我们必须现在检查，如果配置 $F \mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$ 是类型正确的，那么它要么是可约的，要么是一个值。

我们首先检查每一个类型为 $\Pi \mathrm{T}$ 的良好类型值都是一个记录值，也就是说，它要么是 $\left\{\mathrm{v}^{\prime}\right\}$ 的形式，要么是 $\left\{\mathrm{v}^{\prime \prime}\right.$ 与 $\left.\ell^{\prime}=\mathrm{v}^{\prime}\right\}$ 的形式。实际上，假设 $\Gamma_{0}$ 在 $\llbracket \mathrm{v}: \Pi \mathrm{T} \rrbracket$ 中是可满足的。那么，$v$ 不能是一个程序变量，因为一个良好类型的值必须是闭合的；$v$ 不能是一个内存位置 $m$，否则 ref $M(m) \leq \Pi \mathrm{T}$ 就是可以满足的——但顶级类型构造器 ref 和 $\Pi$ 是不兼容的（因为 $\Pi$ 是孤立的）；$v$ 不能是一个构造器或原语的部分应用，也不能是一个 $\lambda$-抽象，因为否则 $\mathrm{T}^{\prime} \rightarrow \mathrm{T}^{\prime \prime} \leq \Pi \mathrm{T}$ 就是可以满足的，但顶级类型构造器 $\rightarrow$ 和 $\Pi$ 是不兼容的（因为它们都是孤立的）；因此，$v$ 必须是 $\{\mathrm{v}\}$ 或 $\{\mathrm{w}$ 与 $\ell=\mathrm{v}\}$ 的形式，因为这是唯一剩下的情况。

接下来，我们注意到，根据约束生成规则，如果配置 $\mathrm{c}_{1} \ldots \mathrm{v}_{k} / \mu$ 是类型良好的，那么形式的约束 let $\Gamma_{0} ; \operatorname{ref} M$ in $\left(\mathrm{c} \preceq \mathrm{x}_{1} \rightarrow \ldots \rightarrow \mathrm{x}_{k} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}_{1}: \mathrm{x}_{1} \rrbracket \wedge \ldots \wedge \llbracket \mathrm{v}_{k}: \mathrm{x}_{k} \rrbracket\right)$ 是可满足的。我们现在按 $\mathrm{c}$ 的不同情况进行推理。

病例c是{}". 我们可以假设k大于等于2，因为否则，该表达式是一个值。那么Γ₀(c)是∀XY. X → Π(∂X)，所以根据C-INID和C-ARROw，上述约束蕴含存在X.（Π(∂X) ≤ X₂ → ... → T），这由C-Class-I蕴含为假，因为"→"和"Π"是不兼容的。因此，这种情况不可能发生。

案例c是{·}，其中ℓ=·。与之前的案例相似。

情况c是·{ℓ}。我们可以假设k≥1，因为否则，该表达式是一个值。那么Γ0(c)是∀XY. Π(ℓ: X ; Y) → X，所以根据C-INID和C-ARRow规则，上述约束蕴含着 let Γ0 ; ref M in (存在XY.(X1 ≤ Π(ℓ: X ; Y)) ∧ [v1: X1])，根据引理1.6.3，这又蕴含着 let Γ0 ; ref M in 存在XY. [v1: Π(ℓ: X ; Y)]。因此v1是一个记录值，即是以下形式之一：{v'}，配置可约至v'；或者形式为{v''}，其中{ℓ'=v'}，配置可约至v'或v''{ℓ}。

1.11.17 解：我们为所有不同标签对的集合添加一个析构函数 $\cdot\left[\ell_{1} \leftrightarrow \ell_{2}\right]$，其元数为1，具有以下语义：

$$
\begin{array}{rr}
\{\mathrm{v}\}\left[\ell_{1} \leftrightarrow \ell_{2}\right] \xrightarrow{\delta} \mathrm{v} \\
\{\mathrm{w} \text { with } \ell=\mathrm{v}\}\left[\ell_{1} \leftrightarrow \ell_{2}\right] \xrightarrow{\delta}\left\{\mathrm{w}\left[\ell_{1} \leftrightarrow \ell_{2}\right] \text { with } \ell=\mathrm{v}\right\} & \text { if } \ell \notin\left\{\ell_{1}, \ell_{2}\right\} \\
\{\mathrm{w} \text { with } \ell=\mathrm{v}\}\left[\ell_{1} \leftrightarrow \ell_{2}\right] \xrightarrow{\delta}\left\{\mathrm{w}\left[\ell_{1} \leftrightarrow \ell_{2}\right] \text { with } \bar{\ell}=\mathrm{v}\right\} & \text { if }\{\ell, \bar{\ell}\}=\left\{\ell_{1}, \ell_{2}\right\}
\end{array}
$$

初始环境 $\Gamma_{0}$ 必须用以下类型假设进行扩展：

$$
\cdot\left[\ell_{1} \leftrightarrow \ell_{2}\right]: \quad \forall \mathrm{X}_{1} \mathrm{X}_{2} \mathrm{Y} \cdot \Pi\left(\ell_{1}: \mathrm{X}_{1} ; \ell_{2}: \mathrm{X}_{2} ; \mathrm{Y}\right) \rightarrow \Pi\left(\ell_{1}: \mathrm{X}_{2} ; \ell_{2}: \mathrm{X}_{1} ; \mathrm{Y}\right)
$$

我们必须然后检查新原语的对象减少。由于我们只添加了一个构造器，因此只需检查新原语的前进性，即形式的良好类型表达式 $\left[\ell_{1} \leftrightarrow \ell_{2}\right] \mathrm{v}_{1} \ldots \mathrm{v}_{n}$ 要么是值，要么可以进一步减少。两部分都很容易，与练习1.11.16中的相应部分相似。

1.11.18 解法：有几个解法。其中之一是假设行标签上有一个固定的全序，只保留作为构造器的 $\ell^{\kappa, L}$ 使得 $\ell<L$，即对所有 $\ell^{\prime} \in L$ 都有 $\ell<\ell^{\prime}$；其他常量 $\ell^{\kappa, L}$ 使得 $\ell \nless L$ 的则从构造器移动到销毁器的状态，并伴随以下归约规则集：

$$
\left\{\left\{\mathrm{w} \text { with } \ell^{\prime}=\mathrm{v}^{\prime}\right\} \text { with } \ell=\mathrm{v}\right\} \xrightarrow{\delta}\left\{\{\mathrm{w} \text { with } \ell=\mathrm{v}\} \text { with } \ell^{\prime}=\mathrm{v}^{\prime}\right\}
$$

(RD-TRANSPOSE)

对于所有标签 $\ell$ 和 $\ell^{\prime}$，使得 $\ell^{\prime}<\ell$ 且

$$
\left\{\left\{\mathrm{w} \text { with } \ell=\mathrm{v}^{\prime}\right\} \text { with } \ell=\mathrm{v}\right\} \xrightarrow{\delta}\{\mathrm{w} \text { with } \ell=\mathrm{v}\}
$$

(RD-DISCARD)

对于所有标签 $\ell$。现在很明显，值处于规范形式，这意味着显式字段永远不会重复，并且总是按顺序列出。类型规则不需要改变，因此定义1.7.6中的要求（i）仍然成立。要求（ii）需要检查，特别是对于新的原语 $\ell^{L}$，我们留给读者去验证（对于 $\cdot .\{\ell\}$ 的证明应该保持不变）。

1.11.19 解决方案：让 map 具有类型 $\Pi(\mathrm{X} \rightarrow \mathrm{Y}) \rightarrow \Pi(\mathrm{X}) \rightarrow \Pi(\mathrm{Y})$，并在具有正常形式的语义中使用以下简化规则：

$$
\begin{gathered}
\operatorname{map}\left\{\mathrm{v}^{\prime} \text { with } \ell=\mathrm{v}\right\} \mathrm{w} \xrightarrow{\delta}\left\{\operatorname{map} \mathrm{v}^{\prime} \mathrm{w} \text { with } \ell=\mathrm{v}(\mathrm{w} \cdot\{\ell\})\right\} \\
\operatorname{map} \mathrm{v}\left\{\mathrm{w}^{\prime} \text { with } \ell=\mathrm{w}\right\} \xrightarrow{\delta}\left\{\operatorname{map} \mathrm{v} \mathrm{w}^{\prime} \text { with } \ell=(\mathrm{v} \cdot\{\ell\}) \mathrm{w}\right\} \\
\operatorname{map}\{\mathrm{v}\}\{\mathrm{w}\} \xrightarrow{\delta}\{\mathrm{v} \mathrm{w}\}
\end{gathered}
$$

1.11.22 解决方案：为确保字段不在扩展的参数中存在，只需按照以下方式限制其类型假设即可：

$$
\langle\cdot \text { with } \ell=\cdot\rangle: \forall \mathrm{Xx}^{\prime} \mathrm{Y} . \Pi(\ell: \text { abs } ; \mathrm{Y}) \rightarrow \mathrm{X}^{\prime} \rightarrow \Pi\left(\ell: \text { pre } \mathrm{X}^{\prime} ; \mathrm{Y}\right)
$$

要删除现有字段，我们可以使用以下语法糖：

$$
\begin{aligned}
\cdot \backslash \ell \stackrel{\text { def }}{=} & \lambda \mathrm{v} \cdot\{\mathrm{v} \text { with } \ell=\mathrm{abs}\} \\
& : \forall \mathrm{XY} . \Pi(\ell: \mathrm{X} ; \mathrm{Y}) \rightarrow \Pi(\ell: \text { abs } ; \mathrm{Y})
\end{aligned}
$$

以下较弱的类型假设也可以用于确保在移除字段之前该字段始终存在：

$$
\forall X Y . \Pi(\ell: \text { pre } \mathrm{X} ; \mathrm{Y}) \rightarrow \Pi(\ell: \text { abs } ; \mathrm{Y})
$$

1.11.25 解答：这个证明与1.11.16类似，但稍微复杂一些，因为我们也必须检查在访问时标签是否被定义，并且涉及到子类型。

我们同时在这两种模型中进行推理：子类型模型和仅相等模型，也就是说，我们只依赖在这两种模型中都有效的属性。

我们必须首先确保规则重新确立并遵守尊重（定义1.7.5）。

- 重新找到案例：见练习??. 在第??行，字段 $\ell$ 应为 pre $\mathrm{X}_{1}$ 而不是 $\mathrm{X}_{1}$，以及 pre $\mathrm{Y}_{2}$ 而不是 $\mathrm{Y}_{2}$，并且步骤??也使用了预前协方差。
- 跟进案例：证明过程类似。

我们必须检查，如果配置 $F \mathrm{v}_{1} \ldots \mathrm{v}_{k} / \mu$ 是类型正确的，那么它要么是可约的，要么是一个值。

我们首先检查每一个类型为 $\Pi \mathrm{T}$ 的良类型值都是一个记录值，也就是说，它要么是 \langle\rangle 的形式，要么是 $\left\langle\mathrm{v}^{\prime \prime}\right.$ 与 $\left.\ell^{\prime}=\mathrm{v}^{\prime}\right\rangle$ 的形式。见练习1.11.16。

接下来，我们注意到，根据约束生成规则，如果配置 $c v_{1} \ldots v_{k} / \mu$ 是类型正确的，那么形如 let $\Gamma_{0} ; \operatorname{ref} M$ in $\left(\mathrm{c} \preceq \mathrm{x}_{1} \rightarrow \ldots \rightarrow \mathrm{x}_{k} \rightarrow \mathrm{T} \wedge \llbracket \mathrm{v}_{1}: \mathrm{x}_{1} \rrbracket \wedge \ldots \wedge \llbracket \mathrm{v}_{k}: \mathrm{x}_{k} \rrbracket\right)$ 的约束是可满足的。我们现在通过$\mathrm{c}$的案例来进行推理。

案例 c 是 ⟨⟩ 或 ⟨· with ℓ=·⟩。见练习 1.11.16。

情况c是$\cdot\langle\ell\rangle$。我们可以假设$k \geq 1$，因为否则表达式是一个值。那么$\Gamma_{0}(\mathrm{c})$是$\forall \mathrm{XY} . \Pi(\ell$：pre $\mathrm{X} ; \mathrm{Y}) \rightarrow \mathrm{X}$，因此由C-INID和C-ARRow规则，上面的约束蕴含着 let $\Gamma_{0} ; \operatorname{ref} M$ in $(\exists \mathrm{XY} .(\mathrm{X}_{1} \leq \Pi(\ell:\text{pre} \mathrm{X} ; \mathrm{Y})\rangle) \wedge \llbracket \mathrm{v}_{1}: \mathrm{X}_{1} \rrbracket)$，根据引理1.6.3，这又蕴含着 let $\Gamma_{0} ; \operatorname{ref} M$ in $\exists \mathrm{XY} . \llbracket \mathrm{v}_{1}: \Pi(\ell:\text{pre} \mathrm{X} ; \mathrm{Y}) \rrbracket$。因此$\mathrm{v}_{1}$是一个记录值，即要么是$\langle\rangle$的形式，要么是$\left\langle\mathrm{v}^{\prime \prime}\right.$的形式，其中$\left.\ell=\mathrm{v}^{\prime}\right\rangle$。实际上，前者情况不可能发生，因为 let $\Gamma_{0} ; \operatorname{ref} M$ in $\exists X Y . \llbracket\langle\rangle: \Pi(\ell:\text{pre} X ; Y)】蕴含着 \exists X Y \Pi(\partial a b s) \leq \Pi(\ell$：pre X;$)$，通过C-INID和C-IN*规则，这又蕴含着 \exists$ X.abs $\leq$ pre $\mathrm{X}$，通过C-Row-DL和$\Pi$以及$\ell$的协变性。然而，这个约束等价于假，因为$\phi(\mathrm{abs}) \leq \phi$(pre $\mathrm{X}$)在任何地面赋值$\phi$中都不成立。因此$\mathrm{v}_{1}$是$\left\langle\mathrm{v}^{\prime \prime}\right.$的形式，其中$\left.\ell^{\prime}=\mathrm{v}^{\prime}\right\rangle$，如果$\ell^{\prime}$是$\ell$，则配置可以简化为$\mathrm{v}^{\prime}$，否则简化为$\mathrm{v}^{\prime \prime}$。

[^0]：本章（目前尚未完成）的配套代码可以在 http://pauillac.inria.fr/remy/mlrow/ 找到。由于篇幅原因，包括证明、习题等在内的某些材料并未包含在此版本中。将来，包含这些遗漏材料的完整版本将在同一地址提供。尽管有这些省略，但这一章节相对于本杰明的100页限制来说仍然篇幅过长：我们目前有大约135页的文本和15页的习题解答。我们非常欢迎校对者就如何在不严重损害其兴趣或可读性的情况下缩短这一章节提出意见和建议。

