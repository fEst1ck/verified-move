<TeXmacs|2.1.1>

<style|generic>

<\body>
  <section|Definitions>

  <subsection|Identifiers>

  <math|<tabular|<tformat|<table|<row|<cell|f>|<cell|\<in\>>|<cell|FieldName>>|<row|<cell|x>|<cell|\<in\>>|<cell|VarName>>>>>>

  <subsection|Values>

  <math|<tabular|<tformat|<table|<row|<cell|u>|<cell|\<in\>>|<cell|UnrestrictedValue>>|<row|<cell|v>|<cell|\<in\>>|<cell|Value>>|<row|<cell|r>|<cell|\<in\>>|<cell|Reference>>>>>>

  <subsection|Memory>

  <math|<tabular|<tformat|<table|<row|<cell|M>|<cell|\<in\>>|<cell|Memory>|<cell|=>|<cell|LocalMemory\<times\>GlobalMemory>>|<row|<cell|>|<cell|>|<cell|LocalMemory>|<cell|=>|<cell|Var\<rightharpoonup\>RuntimeVal>>|<row|<cell|>|<cell|>|<cell|GlobalMemory>|<cell|=>|<cell|AccountAddr\<rightharpoonup\>Account>>|<row|<cell|>|<cell|>|<cell|Account>|<cell|=>|<cell|ModuleName\<rightharpoonup\>Module>>|<row|<cell|>|<cell|>|<cell|Module>|<cell|=>|<cell|StructName\<rightharpoonup\>StructSig>>|<row|<cell|>|<cell|>|<cell|StructSig>|<cell|=>|<cell|Kind\<times\><around*|(|FieldName\<times\>NonRefType|)><rsup|*\<ast\>>>>>>>><inactive*|>

  We define <math|M<around*|(|l|)>> to be the value stored at <math|l> in
  memory <math|M>, where <math|l> could be a local variable or a reference.
  We define <math|M<around*|[|l\<mapsto\>v|]>> to be the memory with <math|l>
  updated to have value <math|v>, and otherwise identical with <math|M>. We
  use <math|M\\x> to denote the memory with <math|x> removed, and otherwise
  identical with <math|M>.

  <section|Judgements>

  <\big-table|<tabular|<tformat|<cwith|4|4|1|1|cell-bborder|0ln>|<cwith|4|4|1|1|cell-lborder|0ln>|<cwith|4|4|1|1|cell-rborder|1ln>|<cwith|4|4|2|2|cell-lborder|1ln>|<cwith|1|1|1|1|cell-tborder|1ln>|<cwith|1|1|1|1|cell-lborder|0ln>|<cwith|1|1|2|2|cell-tborder|1ln>|<cwith|1|1|2|2|cell-bborder|1ln>|<cwith|1|1|2|2|cell-lborder|1ln>|<cwith|1|1|1|1|cell-rborder|1ln>|<cwith|1|1|2|2|cell-rborder|0ln>|<cwith|3|3|1|1|cell-bborder|0ln>|<cwith|4|4|1|1|cell-tborder|0ln>|<cwith|3|3|1|1|cell-lborder|0ln>|<cwith|3|3|2|2|cell-tborder|0ln>|<cwith|3|3|2|2|cell-bborder|0ln>|<cwith|4|4|2|2|cell-tborder|0ln>|<cwith|3|3|2|2|cell-lborder|1ln>|<cwith|3|3|1|1|cell-rborder|1ln>|<cwith|3|3|2|2|cell-rborder|0ln>|<cwith|2|2|1|1|cell-tborder|1ln>|<cwith|1|1|1|1|cell-bborder|1ln>|<cwith|2|2|1|1|cell-bborder|0ln>|<cwith|3|3|1|1|cell-tborder|0ln>|<cwith|2|2|1|1|cell-lborder|0ln>|<cwith|2|2|1|1|cell-rborder|1ln>|<cwith|2|2|2|2|cell-lborder|1ln>|<table|<row|<cell|<strong|Judgement>>|<cell|<strong|Meaning>>>|<row|<cell|<math|r
  q>>|<cell|reference <math|r> has mutability
  <math|q>>>|<row|<cell|<math|M\<vartriangleright\>\<space\>\<kappa\>
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
    \<tau\><around*|{|f<rsub|1>:\<tau\><rsub|1>,\<ldots\>,f<rsub|n>:\<tau\><rsub|n>|}>|<around*|\<langle\>|M,<around*|[|v<rsub|i>|]><rsup|n><rsub|i=1>\<colons\>S|\<rangle\>><long-arrow|\<rubber-rightarrow\>|Pack<around*|\<langle\>|\<tau\>|\<rangle\>>><around*|\<langle\>|M,<strong|resource>
    \<tau\><around*|{|f<rsub|1>:v<rsub|1>,\<ldots\>,f<rsub|n>:v<rsub|n>|}>\<colons\>S|\<rangle\>>>
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
    <associate|auto-1|<tuple|1|1|../.TeXmacs/texts/scratch/no_name_27.tm>>
    <associate|auto-2|<tuple|1.1|1|../.TeXmacs/texts/scratch/no_name_27.tm>>
    <associate|auto-3|<tuple|1.2|1|../.TeXmacs/texts/scratch/no_name_27.tm>>
    <associate|auto-4|<tuple|1.3|1|../.TeXmacs/texts/scratch/no_name_27.tm>>
    <associate|auto-5|<tuple|2|1|../.TeXmacs/texts/scratch/no_name_27.tm>>
    <associate|auto-6|<tuple|1|1|../.TeXmacs/texts/scratch/no_name_27.tm>>
    <associate|auto-7|<tuple|3|2|../.TeXmacs/texts/scratch/no_name_27.tm>>
    <associate|auto-8|<tuple|3.1|2|../.TeXmacs/texts/scratch/no_name_27.tm>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|table>
      <tuple|normal|<\surround|<hidden-binding|<tuple>|1>|>
        \;
      </surround>|<pageref|auto-6>>
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Definitions>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <with|par-left|<quote|1tab>|1.1<space|2spc>Identifiers
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>>

      <with|par-left|<quote|1tab>|1.2<space|2spc>Values
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|1tab>|1.3<space|2spc>Memory
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Judgements>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Operational
      Semantics> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7><vspace|0.5fn>

      <with|par-left|<quote|1tab>|3.1<space|2spc>Local Instructions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>
    </associate>
  </collection>
</auxiliary>