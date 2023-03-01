<TeXmacs|2.1.1>

<style|generic>

<\body>
  <section|Definitions>

  <subsection|Identifiers>

  <math|<tabular|<tformat|<table|<row|<cell|>|<cell|>|<cell|ModuleName>>|<row|<cell|>|<cell|>|<cell|StructName>>|<row|<cell|f>|<cell|\<in\>>|<cell|FieldName>>|<row|<cell|x>|<cell|\<in\>>|<cell|VarName>>>>>>

  <subsection|Types and Kinds>

  <math|<tabular|<tformat|<table|<row|<cell|>|<cell|>|<cell|Kind>|<cell|=>|<cell|<strong|resource><text|
  \| <math|<strong|unrestricted>>>>>|<row|<cell|>|<cell|>|<cell|ModuleId>|<cell|=>|<cell|AccountAddr\<times\>ModuleName>>|<row|<cell|s>|<cell|\<in\>>|<cell|StructID>|<cell|=>|<cell|ModuleID\<times\>StructName>>|<row|<cell|>|<cell|>|<cell|StructType>|<cell|=>|<cell|StructID>>|<row|<cell|>|<cell|>|<cell|PrimitiveType>|<cell|=>|<cell|AccountAddr\<cup\>Bool\<cup\>Unsigned64\<cup\>Bytes>>|<row|<cell|a>|<cell|\<in\>>|<cell|AccountAddr>|<cell|>|<cell|>>|<row|<cell|b>|<cell|\<in\>>|<cell|Bool>|<cell|>|<cell|>>|<row|<cell|n>|<cell|\<in\>>|<cell|Unsigned64>|<cell|>|<cell|>>|<row|<cell|<wide|b|\<vect\>>>|<cell|\<in\>>|<cell|Bytes>|<cell|>|<cell|>>|<row|<cell|\<tau\>>|<cell|\<in\>>|<cell|NonRefType>|<cell|=>|<cell|StructType\<times\>Primitive>>|<row|<cell|>|<cell|>|<cell|Type>|<cell|=>|<cell|<text|<math|\<tau\>>
  \| <math|&mut \<tau\>> \| <math|& \<tau\>> >>>>>>>

  <subsection|Values>

  <math|<tabular|<tformat|<table|<row|<cell|r
  v>|<cell|\<in\>>|<cell|Resource>|<cell|=>|<cell|StructID\<times\>Tag\<times\>Value<rsup|\<ast\>>>>|<row|<cell|>|<cell|>|<cell|Struct>|<cell|=>|<cell|StructID\<times\>UnrestrictedValue<rsup|\<ast\>>>>|<row|<cell|>|<cell|>|<cell|PrimitiveValue>|<cell|=>|<cell|<text|<math|a>
  \| <math|b> \| <math|n> \| <math|<wide|b|\<vect\>>>>>>|<row|<cell|u>|<cell|\<in\>>|<cell|UnrestrictedValue>|<cell|=>|<cell|Struct\<cup\>PrimitiveValue>>|<row|<cell|v>|<cell|\<in\>>|<cell|Value>|<cell|=>|<cell|Resource\<cup\>UnrestrictedValue>>|<row|<cell|r>|<cell|\<in\>>|<cell|Reference>|<cell|=>|<cell|Root\<times\>Path\<times\>Qualifier>>|<row|<cell|>|<cell|>|<cell|Root>|<cell|=>|<cell|<text|<math|x>
  \| <math|s>>>>|<row|<cell|p>|<cell|\<in\>>|<cell|Path>|<cell|=>|<cell|f<rsup|\<ast\>>>>|<row|<cell|q>|<cell|\<in\>>|<cell|Qualifier>|<cell|=>|<cell|<text|<strong|mut>
  \| <strong|immut>>>>|<row|<cell|>|<cell|>|<cell|RuntimeValue>|<cell|=>|<cell|<text|<math|v>
  \| <math|r>>>>>>>>

  <subsection|Memory>

  <math|<tabular|<tformat|<table|<row|<cell|M>|<cell|\<in\>>|<cell|Memory>|<cell|=>|<cell|LocalMemory\<times\>GlobalMemory>>|<row|<cell|>|<cell|>|<cell|LocalMemory>|<cell|=>|<cell|Var\<rightharpoonup\>RuntimeVal>>|<row|<cell|>|<cell|>|<cell|GlobalMemory>|<cell|=>|<cell|AccountAddr\<rightharpoonup\>Account>>|<row|<cell|>|<cell|>|<cell|Account>|<cell|=>|<cell|ModuleName\<rightharpoonup\>Module>>|<row|<cell|>|<cell|>|<cell|Module>|<cell|=>|<cell|StructName\<rightharpoonup\>StructSig>>|<row|<cell|>|<cell|>|<cell|StructSig>|<cell|=>|<cell|Kind\<times\><around*|(|FieldName\<times\>NonRefType|)><rsup|*\<ast\>>>>>>>><inactive*|>

  We write <math|M<around*|(|l|)>> to be the value stored at <math|l> in
  memory <math|M>, where <math|l> could be a local variable or a reference.
  We write <math|M<around*|[|l\<mapsto\>v|]>> to be the memory with <math|l>
  updated to have value <math|v>, and otherwise identical with <math|M>. We
  use <math|M\\x> to denote the memory with <math|x> removed, and otherwise
  identical with <math|M>.

  <subsection|Local Evaluation State>

  <math|<tabular|<tformat|<table|<row|<cell|\<sigma\>>|<cell|\<in\>>|<cell|LocalState>|<cell|=>|<cell|<around*|\<langle\>|M,S|\<rangle\>>>>|<row|<cell|S>|<cell|\<in\>>|<cell|LocalStack>|<cell|=>|<cell|RuntimeValue<rsup|\<ast\>>>>|<row|<cell|l>|<cell|\<in\>>|<cell|Location>|<cell|=>|<cell|<text|<math|x.p>
  \| <math|s.p> \| <math|n.p> >>>>>>>

  We write <math|\<sigma\><around*|(|l|)>=v> if the (possibly runtime) value
  stored at <math|l> is <math|v>.

  <\definition>
    A local state <math|\<sigma\>> is tag-consistent if
    <math|\<sigma\><around*|(|l<rsub|1>|)>=r v<rsub|1>>,
    <math|\<sigma\><around*|(|l<rsub|2>|)>=r v<rsub|2>> and
    <math|tag<around*|(|r v<rsub|1>|)>=tag<around*|(|r v<rsub|2>|)>> implies
    that <math|l<rsub|1>=l<rsub|2>>. That is, each resource value hold in
    <math|\<sigma\>> has a unique tag.
  </definition>

  <section|Judgements>

  <\big-table|<tabular|<tformat|<cwith|5|5|1|1|cell-bborder|0ln>|<cwith|5|5|1|1|cell-lborder|0ln>|<cwith|5|5|1|1|cell-rborder|1ln>|<cwith|5|5|2|2|cell-lborder|1ln>|<cwith|1|1|1|1|cell-tborder|1ln>|<cwith|1|1|1|1|cell-lborder|0ln>|<cwith|1|1|2|2|cell-tborder|1ln>|<cwith|1|1|2|2|cell-bborder|1ln>|<cwith|1|1|2|2|cell-lborder|1ln>|<cwith|1|1|1|1|cell-rborder|1ln>|<cwith|1|1|2|2|cell-rborder|0ln>|<cwith|4|4|1|1|cell-bborder|0ln>|<cwith|5|5|1|1|cell-tborder|0ln>|<cwith|4|4|1|1|cell-lborder|0ln>|<cwith|4|4|2|2|cell-tborder|0ln>|<cwith|4|4|2|2|cell-bborder|0ln>|<cwith|5|5|2|2|cell-tborder|0ln>|<cwith|4|4|2|2|cell-lborder|1ln>|<cwith|4|4|1|1|cell-rborder|1ln>|<cwith|4|4|2|2|cell-rborder|0ln>|<cwith|2|2|1|1|cell-tborder|1ln>|<cwith|1|1|1|1|cell-bborder|1ln>|<cwith|2|2|1|1|cell-lborder|0ln>|<cwith|2|2|1|1|cell-rborder|1ln>|<cwith|2|2|2|2|cell-lborder|1ln>|<cwith|3|3|1|1|cell-tborder|0ln>|<cwith|2|2|1|1|cell-bborder|0ln>|<cwith|3|3|1|1|cell-bborder|0ln>|<cwith|4|4|1|1|cell-tborder|0ln>|<cwith|3|3|1|1|cell-lborder|0ln>|<cwith|3|3|1|1|cell-rborder|1ln>|<cwith|3|3|2|2|cell-lborder|1ln>|<table|<row|<cell|<strong|Judgement>>|<cell|<strong|Meaning>>>|<row|<cell|<math|r
  q>>|<cell|reference <math|r> has mutability
  <math|q>>>|<row|<cell|<math|M\<vartriangleright\>t
  <strong|Fresh>>>|<cell|tag <math|t> is fresh in
  <math|M>>>|<row|<cell|<math|M\<vartriangleright\>\<space\>\<kappa\>
  \<tau\><around*|{|f<rsub|1>:\<tau\><rsub|1>,\<ldots\>,f<rsub|n>:\<tau\><rsub|n>|}>>>|<cell|In
  memory <math|M> struct type <math|\<tau\>> has kind <math|\<kappa\>>, field
  name <math|f<rsub|i>> and field types <math|\<tau\><rsub|i>>>>|<row|<cell|<math|<around*|\<langle\>|M,S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|i><around*|\<langle\>|M<rprime|'>,S<rprime|'>|\<rangle\>>>>|<cell|state
  <math|<around*|\<langle\>|M,S|\<rangle\>>> steps to
  <math|<around*|\<langle\>|M,S|\<rangle\>>> after executing instruction
  <math|i>>>>>>>
    \;
  </big-table>

  <section|Operational Semantics>

  <subsection|Local Instructions>

  <\equation*>
    <frac|M<around*|(|x|)>=v\<vee\>M<around*|(|x|)>=r|<around*|\<langle\>|M,S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|MvLoc<around*|\<langle\>|x|\<rangle\>>><around*|\<langle\>|M\\x,M<around*|(|x|)>\<colons\>S|\<rangle\>>>
    <strong|MvLoc>
  </equation*>

  <\equation*>
    <frac|M<around*|(|x|)>=u\<vee\>M<around*|(|x|)>=r|<around*|\<langle\>|M,S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|CpLoc<around*|\<langle\>|x|\<rangle\>>><around*|\<langle\>|M,M<around*|(|x|)>\<colons\>S|\<rangle\>>>
    <strong|CpLoc>
  </equation*>

  <\equation*>
    <frac|s=u\<vee\>s=r|<around*|\<langle\>|M,s\<colons\>S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|StLoc<around*|\<langle\>|x|\<rangle\>>><around*|\<langle\>|M<around*|[|x\<mapsto\>s|]>,S|\<rangle\>>>
    <strong|StLoc>
  </equation*>

  \;

  <\equation*>
    <frac|M<around*|(|x|)>=v|<around*|\<langle\>|M,S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|BorrowLoc<around*|\<langle\>|x|\<rangle\>>><around*|\<langle\>|M,<strong|ref>
    <around*|\<langle\>|x,<around*|[||]>,<strong|mut>|\<rangle\>>|\<rangle\>>>
    <strong|BorrowLoc>
  </equation*>

  <\equation*>
    <frac|r=<strong|ref ><around*|\<langle\>|l,p,q|\<rangle\>>|<around*|\<langle\>|M,r\<colons\>S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|BorrowField<around*|\<langle\>|f|\<rangle\>>><around*|\<langle\>|M,<strong|ref>
    <around*|\<langle\>|l,p\<colons\>f,q|\<rangle\>>\<colons\>S|\<rangle\>>>
    <strong|BorrowField>
  </equation*>

  <\equation*>
    <frac|r=<strong|ref> <around*|\<langle\>|l,p,q|\<rangle\>>|<around*|\<langle\>|M,r\<colons\>S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|FreezeRef><around*|\<langle\>|M,<strong|ref>
    <around*|\<langle\>|M,<strong|ref> <around*|\<langle\>|l,p,<strong|immut>|\<rangle\>>|\<rangle\>>|\<rangle\>>>
    <strong|FreezeRef>
  </equation*>

  <\equation*>
    <frac|M<around*|(|r|)>=u|<around*|\<langle\>|M,r\<colons\>S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|ReadRef><around*|\<langle\>|M,u\<colons\>S|\<rangle\>>>
    <strong|ReadRef>
  </equation*>

  <\equation*>
    <frac|r <strong|mut><space|1em>M<around*|(|r|)>=u|<around*|\<langle\>|M,v\<colons\>r\<colons\>S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|WriteRef><around*|\<langle\>|M<around*|[|r\<mapsto\>v|]>,S|\<rangle\>>>
    <strong|WriteRef>
  </equation*>

  <\equation*>
    <frac|s=u\<vee\>s=r|<around*|\<langle\>|M,s\<colons\>S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|Pop><around*|\<langle\>|M,S|\<rangle\>>>
    <strong|Pop>
  </equation*>

  <\equation*>
    <frac|M\<vartriangleright\>\<space\><strong|resource>
    \<tau\><around*|{|f<rsub|1>:\<tau\><rsub|1>,\<ldots\>,f<rsub|n>:\<tau\><rsub|n>|}><space|1em>M\<vartriangleright\>t
    <strong|Fresh>|<around*|\<langle\>|M,<around*|[|v<rsub|i>|]><rsup|n><rsub|i=1>\<colons\>S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|Pack<around*|\<langle\>|\<tau\>|\<rangle\>>><around*|\<langle\>|M,<around*|\<langle\>|<strong|resource>
    \<tau\><around*|{|f<rsub|1>:v<rsub|1>,\<ldots\>,f<rsub|n>:v<rsub|n>|}>\<colons\>S,t|\<rangle\>>|\<rangle\>>>
    <strong|PackR>
  </equation*>

  <\equation*>
    <frac|M\<vartriangleright\>\<space\><strong|unrestricted>
    \<tau\><around*|{|f<rsub|1>:\<tau\><rsub|1>,\<ldots\>,f<rsub|n>:\<tau\><rsub|n>|}>|<around*|\<langle\>|M,<around*|[|u<rsub|i>|]><rsup|n><rsub|i=1>\<colons\>S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|Pack<around*|\<langle\>|\<tau\>|\<rangle\>>><around*|\<langle\>|M,<strong|resource>
    \<tau\><around*|{|f<rsub|1>:u<rsub|1>,\<ldots\>,f<rsub|n>:u<rsub|n>|}>\<colons\>S|\<rangle\>>>
    <strong|PackU>
  </equation*>

  <\equation*>
    <frac||<around*|\<langle\>|M,\<kappa\>
    \<tau\><around*|{|f<rsub|1>:v<rsub|1>,\<ldots\>,f<rsub|n>:v<rsub|n>|}>\<colons\>S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|Unpack><around*|\<langle\>|M,v<rsub|1>\<colons\>\<cdots\>\<colons\>v<rsub|n>\<colons\>S|\<rangle\>>>
    <strong|Unpack>
  </equation*>

  <\equation*>
    <frac||<around*|\<langle\>|M,S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|LoadConst<around*|\<langle\>|a|\<rangle\>>><around*|\<langle\>|M,a\<colons\>S|\<rangle\>>>
    <strong|LoadConst>
  </equation*>

  <\equation*>
    <frac|<around*|\||op|\|>=n|<around*|\<langle\>|M,u<rsub|1>\<colons\>\<cdots\>\<colons\>u<rsub|n>\<colons\>S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|Op><around*|\<langle\>|M,op<around*|(|u<rsub|1>,\<ldots\>,u<rsub|n>|)>\<colons\>S|\<rangle\>>>
    <strong|StackOp>
  </equation*>
</body>

<\initial>
  <\collection>
    <associate|page-medium|paper>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-10|<tuple|3.1|2>>
    <associate|auto-2|<tuple|1.1|1>>
    <associate|auto-3|<tuple|1.2|1>>
    <associate|auto-4|<tuple|1.3|1>>
    <associate|auto-5|<tuple|1.4|1>>
    <associate|auto-6|<tuple|1.5|1>>
    <associate|auto-7|<tuple|2|2>>
    <associate|auto-8|<tuple|1|2>>
    <associate|auto-9|<tuple|3|2>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|table>
      <tuple|normal|<\surround|<hidden-binding|<tuple>|1>|>
        \;
      </surround>|<pageref|auto-8>>
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Definitions>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <with|par-left|<quote|1tab>|1.1<space|2spc>Identifiers
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>>

      <with|par-left|<quote|1tab>|1.2<space|2spc>Types and Kinds
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|1tab>|1.3<space|2spc>Values
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <with|par-left|<quote|1tab>|1.4<space|2spc>Memory
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <with|par-left|<quote|1tab>|1.5<space|2spc>Local Evaluation State
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Judgements>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Operational
      Semantics> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9><vspace|0.5fn>

      <with|par-left|<quote|1tab>|3.1<space|2spc>Local Instructions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>>
    </associate>
  </collection>
</auxiliary>