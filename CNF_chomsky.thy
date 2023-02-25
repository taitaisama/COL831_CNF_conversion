theory CNF_chomsky
  imports Main
begin

section "Basic modelling"

datatype ('n, 't) Elem = NT "'n" | T "'t"
type_synonym ('n, 't) PartialEvaluation = "('n, 't) Elem list"
type_synonym ('n, 't) Rule = "'n \<times> ('n, 't) PartialEvaluation"
type_synonym ('n, 't) Rules = "('n, 't) Rule set"
type_synonym ('n, 't) CFG = "'n \<times> ('n, 't) Rules"

definition Productions :: "('n, 't)Rules \<Rightarrow> (('n, 't)PartialEvaluation \<times> ('n, 't)PartialEvaluation) set"
  where "Productions G = {(l @ [NT(N)] @ r, l @ rhs @ r) | l N r rhs. (N, rhs) \<in> G}"

definition ProductionStep :: "('n, 't) PartialEvaluation \<Rightarrow> ('n, 't)Rules \<Rightarrow> ('n, 't)PartialEvaluation \<Rightarrow> bool"  ("_ -_\<rightarrow> _" [60, 61, 60] 61) 
  where "w -G\<rightarrow> w' \<equiv> (w, w') \<in> Productions G"

fun ProducesInN :: "('n, 't) PartialEvaluation \<Rightarrow> ('n, 't) Rules \<Rightarrow> nat \<Rightarrow> ('n, 't) PartialEvaluation \<Rightarrow> bool" ("_ -_\<rightarrow>\<^sup>_ _" [60, 61, 61, 60] 61)
  where "s -G\<rightarrow>\<^sup>0 t = (s = t)" | 
        "ProducesInN s G (Suc(n)) t = (\<exists> r. s -G\<rightarrow> r \<and> s -G\<rightarrow>\<^sup>n t)"

definition Produces :: "('n, 't) PartialEvaluation \<Rightarrow> ('n, 't) Rules \<Rightarrow> ('n, 't) PartialEvaluation \<Rightarrow> bool" ("_ -_\<rightarrow>\<^sup>* _" [60, 61, 60] 61) 
  where "w -G\<rightarrow>\<^sup>* w' \<equiv> \<exists> n. w -G\<rightarrow>\<^sup>n w'"

definition IsTerminalWord :: "('n, 't) Elem list \<Rightarrow> bool"
  where "IsTerminalWord El \<equiv> \<not>(\<exists> a. NT(a) \<in> set El)"

definition Language :: "'n \<Rightarrow> ('n, 't) Rules \<Rightarrow> (('n, 't) Elem list) set" ("\<lbrakk>_\<rbrakk>\<^sub>_" [60, 61])
  where "\<lbrakk>S\<rbrakk>\<^sub>G = { w | w. IsTerminalWord w \<and> [NT(S)] -G\<rightarrow>\<^sup>* w}"

definition Lang :: "('n, 't) CFG \<Rightarrow> (('n, 't) Elem list) set" ("\<lbrakk>_\<rbrakk>")
  where "Lang G \<equiv> {w | w S R. w \<in> \<lbrakk>S\<rbrakk>\<^sub>R \<and> (S, R) = G}"

definition NTInRule :: "'n \<Rightarrow> ('n, 't) Rule \<Rightarrow> bool"
  where "NTInRule N R \<equiv> \<exists> S Rhs. (S, Rhs) = R \<and> (S = N \<or> (NT(N) \<in> set Rhs))"

definition NonTerminals :: "('n, 't) CFG \<Rightarrow> ('n, 't) Elem set"
  where "NonTerminals G = {NT(a) | S Rs a R. (S, Rs) = G \<and> R \<in> Rs \<and> NTInRule a R}"

definition TInRule ::  "'t \<Rightarrow> ('n, 't) Rule \<Rightarrow> bool"
  where "TInRule N R \<equiv> \<exists> S Rhs. (S, Rhs) = R \<and> (T(N) \<in> set Rhs)"

definition Terminals :: "('n, 't) CFG \<Rightarrow> ('n, 't) Elem set"
  where "Terminals G = {T(a) | S Rs a R. (S, Rs) = G \<and> R \<in> Rs \<and> TInRule a R}"

definition transformStart :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool" 
  where "transformStart G1 S0 G2 \<equiv> \<exists> S1 R1 R2. (S1, R1) = G1 
                                   \<and> (S0, R2) = G2 
                                   \<and> NT(S0) \<notin> NonTerminals(G1)
                                   \<and> R2 = insert (S0, [NT(S1)]) R1"

lemma Start_Part1:
    assumes a: "transformStart (S1, R1) S0 (S0, insert (S0, [NT S1]) R1)"
    assumes b: "\<forall>a. NT a \<notin> set x"
    assumes c: "G1 = (S1, R1)"
    assumes d: "[NT S1] -R1\<rightarrow>\<^sup>n x"
    assumes e: "\<forall>a b. (a, b) \<in> R1 \<longrightarrow> a \<noteq> S0 \<and> NT S0 \<notin> set b" 
    assumes f: "G2 = (S0, insert (S0, [NT S1]) R1)"
    shows      "\<exists>n. [NT S0] -insert (S0, [NT S1]) R1\<rightarrow>\<^sup>n x"
  using a and b and c and d and f apply-
  apply(induction n, auto)
  done

lemma Start_Part2:
  assumes a: "transformStart (S1, R1) S0 (S0, insert (S0, [NT S1]) R1)"
  assumes b: "\<forall>a. NT a \<notin> set x"
  assumes c: "G1 = (S1, R1)"
  assumes d: "[NT S0] -insert (S0, [NT S1]) R1\<rightarrow>\<^sup>n x"
  assumes e: "\<forall>a b. (a, b) \<in> R1 \<longrightarrow> a \<noteq> S0 \<and> NT S0 \<notin> set b" 
  assumes f: "G2 = (S0, insert (S0, [NT S1]) R1)"
  shows      "\<exists>n. [NT S1] -R1\<rightarrow>\<^sup>n x"
  using a and b and c and d and f apply-
  apply(induction n, auto)
  done

theorem verifyTransformStart:
  assumes a: "transformStart G1 S0 G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 1: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (unfold transformStart_def NonTerminals_def NTInRule_def Lang_def Language_def Produces_def IsTerminalWord_def, auto, simp add: Start_Part1)
  from a have 2: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (unfold transformStart_def NonTerminals_def NTInRule_def Lang_def Language_def Produces_def IsTerminalWord_def, auto, simp add: Start_Part2)
  from 1 and 2 show ?thesis
    by blast
qed

definition transformTermSingle :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformTermSingle G1 N G2 \<equiv> \<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
                                 (S, Rs1) = G1 
                                 \<and> R1 = (S1, L @ (T(a) # R))
                                 \<and> R2 = (S1, L @ (NT(N) # R))
                                 \<and> R3 = (N, [T a])
                                 \<and> (S, Rs2) = G2 
                                 \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                                 \<and> NT(N) \<notin> NonTerminals(G1)"

lemma Term_Part1:
  assumes a: "R1 = (S1, L @ T a # R)"
  assumes b: "R2 = (S1, L @ NT N # R)"
  assumes c: "R3 = (N, [T a])"
  assumes d: "G1 = (S, Rs1)"
  assumes e: "G2 = (S, Rs2)"
  assumes f: "IsTerminalWord x"
  assumes g: "[NT S] -Rs1\<rightarrow>\<^sup>n x"
  assumes h: "Rs2 = {R2, R3} \<union> (Rs1 - {R1})"
  assumes i: "NT N \<notin> NonTerminals G1"
  shows      "\<exists>n. [NT S] -Rs2\<rightarrow>\<^sup>n x"
  using a and b and c and d and e and f and g and h and i apply-
  apply(induction n, auto, simp add: IsTerminalWord_def)
  done
  
lemma Term_Part2:
  assumes a: "R1 = (S1, L @ T a # R)"
  assumes b: "R2 = (S1, L @ NT N # R)"
  assumes c: "R3 = (N, [T a])"
  assumes d: "G1 = (S, Rs1)"
  assumes e: "G2 = (S, Rs2)"
  assumes f: "IsTerminalWord x"
  assumes g: "[NT S] -Rs2\<rightarrow>\<^sup>n x"
  assumes h: "Rs2 = {R2, R3} \<union> (Rs1 - {R1})"
  assumes i: "NT N \<notin> NonTerminals G1"
  shows      "\<exists>n. [NT S] -Rs1\<rightarrow>\<^sup>n x"
  using a and b and c and d and e and f and g and h and i apply-
  apply(induction n, auto, simp add: IsTerminalWord_def)
  done

theorem verifyTransformTerm: 
  assumes a: "transformTermSingle G1 N G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0: "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
                    (S, Rs1) = G1 
                    \<and> R1 = (S1, L @ (T(a) # R))
                    \<and> R2 = (S1, L @ (NT(N) # R))
                    \<and> R3 = (N, [T a])
                    \<and> (S, Rs2) = G2 
                    \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                    \<and> NT(N) \<notin> NonTerminals(G1)" 
                  (is "\<exists>S R1 R2 R3 Rs1 Rs2 S1 L R a. ?P S R1 R2 R3 Rs1 Rs2 S1 L R a")
    by (simp add: transformTermSingle_def)
  from 0 obtain S R1 R2 R3 Rs1 Rs2 S1 L R a where 1: "?P S R1 R2 R3 Rs1 Rs2 S1 L R a" by blast
  from 1 have 2: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (unfold Lang_def Language_def Produces_def, auto, simp add: Term_Part1)
  from 1 have 3: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (unfold Lang_def Language_def Produces_def, auto, simp add: Term_Part2)
  from 2 and 3 show ?thesis
    using "1" by fastforce
qed

definition transformBinSingle :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformBinSingle G1 N G2 \<equiv> \<exists> S R1 R2 R3 Rs1 Rs2 S1 a b c. 
                                   (S, Rs1) = G1 
                                 \<and> (S, Rs2) = G2 
                                 \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                                 \<and> NT(N) \<notin> NonTerminals(G1)
                                 \<and> R1 = (S1, a # b # c)
                                 \<and> R2 = (S1, a # [NT N])
                                 \<and> R3 = (N, b # c)"

lemma Bin_Part1:
  assumes a: "R1 = (S1, a # b # c)"
  assumes b: "R2 = (S1, [a, NT N])"
  assumes c: "R3 = (N, b # c)"
  assumes d: "G1 = (S, Rs1)"
  assumes e: "G2 = (S, Rs2)"
  assumes f: "IsTerminalWord x"
  assumes g: "x \<in> \<lbrakk>G1\<rbrakk>"
  assumes h: "Rs2 = {R2, R3} \<union> (Rs1 - {R1})"
  assumes i: "NT N \<notin> NonTerminals G1"
  shows      "x \<in> \<lbrakk>G2\<rbrakk>"
proof-
  from g and d have 0: "\<exists> n. [NT S] -Rs1\<rightarrow>\<^sup>n x" (is "\<exists> n. ?P n")
    by (unfold Lang_def Language_def Produces_def, auto)
  then obtain n where 1: "?P n" by blast
  from a and b and c and d and e and f and h and 1 show ?thesis
  by(induction n, simp add: IsTerminalWord_def, auto)
qed

lemma Bin_Part2:
  assumes a: "R1 = (S1, a # b # c)"
  assumes b: "R2 = (S1, [a, NT N])"
  assumes c: "R3 = (N, b # c)"
  assumes d: "G1 = (S, Rs1)"
  assumes e: "G2 = (S, Rs2)"
  assumes f: "IsTerminalWord x"
  assumes g: "x \<in> \<lbrakk>G2\<rbrakk>"
  assumes h: "Rs2 = {R2, R3} \<union> (Rs1 - {R1})"
  assumes i: "NT N \<notin> NonTerminals G1"
  shows      "x \<in> \<lbrakk>G1\<rbrakk>"
proof-
  from g and e have 0: "\<exists> n. [NT S] -Rs2\<rightarrow>\<^sup>n x" (is "\<exists> n. ?P n")
    by (unfold Lang_def Language_def Produces_def, auto)
  then obtain n where 1: "?P n" by blast
  from a and b and c and d and e and f and h and 1 show ?thesis
  by(induction n, simp add: IsTerminalWord_def, auto)
qed

theorem verifyTransformBin: 
  assumes a: "transformBinSingle G1 N G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0: "\<exists>S R1 R2 R3 Rs1 Rs2 S1 a b c. 
                    (S, Rs1) = G1 
                    \<and> (S, Rs2) = G2 
                    \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                    \<and> NT(N) \<notin> NonTerminals(G1)
                    \<and> R1 = (S1, a # b # c)
                    \<and> R2 = (S1, a # [NT N])
                    \<and> R3 = (N, b # c)" 
                  (is "\<exists>S R1 R2 R3 Rs1 Rs2 S1 a b c. ?P S R1 R2 R3 Rs1 Rs2 S1 a b c")
    by (simp add: transformBinSingle_def)
  from 0 obtain S R1 R2 R3 Rs1 Rs2 S1 a b c where 1: "?P S R1 R2 R3 Rs1 Rs2 S1 a b c" by blast
  from 1 have 2: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (smt (verit) Bin_Part1 Lang_def Language_def mem_Collect_eq)
  from 1 have 3: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (smt (verit) Bin_Part2 Lang_def Language_def mem_Collect_eq)
  from 2 and 3 show ?thesis
    by blast
qed

definition DelNTFromRuleSet :: "'n \<Rightarrow> (('n, 't) Rule \<times> ('n, 't) Rule) set"
  where "DelNTFromRuleSet N \<equiv> {((S, l @ NT(N) # r), (S, l @ r)) | S l r. True}\<^sup>*"

definition DelNTFromRule :: "'n \<Rightarrow> ('n, 't) Rule set \<Rightarrow> ('n, 't) Rule set"
  where "DelNTFromRule N R \<equiv> { NR | NR OR. (OR, NR) \<in> DelNTFromRuleSet N \<and> OR \<in> R }"

definition transformDelSingle :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformDelSingle G1 N G2 \<equiv> \<exists> S Rs1 Rs2. 
                                N \<noteq> S 
                                \<and> (S, Rs1) = G1
                                \<and> (S, Rs2) = G2
                                \<and> (N, Nil) \<in> Rs1
                                \<and> Rs2 = (DelNTFromRule N Rs1) - {(N, Nil)}"

lemma Del_Part1:      
  assumes a: "N \<noteq> S"
  assumes b: "(S, Rs1) = G1"
  assumes c: "(S, Rs2) = G2"
  assumes d: "(N, []) \<in> Rs1"
  assumes e: "Rs2 = DelNTFromRule N Rs1 - {(N, [])}"
  assumes g: "x \<in> \<lbrakk>G1\<rbrakk>"
  shows      "x \<in> \<lbrakk>G2\<rbrakk>"
proof-
  from g and b have 0: "\<exists> n. [NT S] -Rs1\<rightarrow>\<^sup>n x" (is "\<exists> n. ?P n")
    by (simp add: Lang_def Language_def Produces_def, auto)
  then obtain n where 1: "?P n" by blast
  from g have 2: "IsTerminalWord x" by (simp add: Lang_def Language_def Produces_def)
  from a and b and c and d and e and 2 and 1 show ?thesis
    by(unfold IsTerminalWord_def, induction n, auto)
qed

lemma Del_Part2:      
  assumes a: "N \<noteq> S"
  assumes b: "(S, Rs1) = G1"
  assumes c: "(S, Rs2) = G2"
  assumes d: "(N, []) \<in> Rs1"
  assumes e: "Rs2 = DelNTFromRule N Rs1 - {(N, [])}"
  assumes g: "x \<in> \<lbrakk>G2\<rbrakk>"
  shows      "x \<in> \<lbrakk>G1\<rbrakk>"
proof-
  from g and c have 0: "\<exists> n. [NT S] -Rs2\<rightarrow>\<^sup>n x" (is "\<exists> n. ?P n")
    by (simp add: Lang_def Language_def Produces_def, auto)
  then obtain n where 1: "?P n" by blast
  from g have 2: "IsTerminalWord x" by (simp add: Lang_def Language_def Produces_def)
  from a and b and c and d and e and 2 and 1 show ?thesis
    by(unfold IsTerminalWord_def, induction n, auto)
qed

theorem verifyTransformDel: 
  assumes a: "transformDelSingle G1 N G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0:  "\<exists>S Rs1 Rs2.
                   N \<noteq> S \<and>
                   (S, Rs1) = G1 \<and>
                   (S, Rs2) = G2 \<and>
                   (N, []) \<in> Rs1 \<and>
                   Rs2 = DelNTFromRule N Rs1 - {(N, [])}" 
                  (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
  by(unfold transformDelSingle_def, auto)
  then obtain S Rs1 Rs2 where 1: "?P S Rs1 Rs2" by blast
  from 1 have 2: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (meson Del_Part1)
  from 1 have 3: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (meson Del_Part2)
  from 2 and 3 show ?thesis
    by blast
qed

definition NewUnitTransRules :: "'n \<Rightarrow> 'n \<Rightarrow> ('n, 't) Rules \<Rightarrow> ('n, 't) Rules"
  where "NewUnitTransRules A B R1 \<equiv> {R2 | R2 Rhs. (B, Rhs) \<in> R1 \<and> (A, Rhs) = R2}"

definition transformUnitSingle :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformUnitSingle G1 A B G2 \<equiv> \<exists> S Rs1 Rs2. 
                                   (S, Rs1) = G1
                                   \<and> (S, Rs2) = G2
                                   \<and> (A, [NT(B)]) \<in> Rs1
                                   \<and> Rs2 = (Rs1 \<union> (NewUnitTransRules A B Rs1)) - {(A, [NT(B)])}"

lemma Unit_Part1 :
  assumes a: "(S, Rs1) = G1"
  assumes b: "(S, Rs2) = G2"
  assumes c: "(A, [NT B]) \<in> Rs1"
  assumes d: "Rs2 = Rs1 \<union> NewUnitTransRules A B Rs1 - {(A, [NT B])}"
  assumes e: "x \<in> \<lbrakk>G1\<rbrakk>"
  shows      "x \<in> \<lbrakk>G2\<rbrakk>"
proof-
  from e and a have 0: "\<exists> n. [NT S] -Rs1\<rightarrow>\<^sup>n x" (is "\<exists> n. ?P n")
    by (simp add: Lang_def Language_def Produces_def, auto)
  then obtain n where 1: "?P n" by blast
  from e have 2: "IsTerminalWord x"
    by (simp add: Lang_def Language_def Produces_def)
  from 1 and 2 and a and b and c show ?thesis
    by (induction n, auto, simp add: IsTerminalWord_def)
qed

lemma Unit_Part2 :
  assumes a: "(S, Rs1) = G1"
  assumes b: "(S, Rs2) = G2"
  assumes c: "(A, [NT B]) \<in> Rs1"
  assumes d: "Rs2 = Rs1 \<union> NewUnitTransRules A B Rs1 - {(A, [NT B])}"
  assumes e: "x \<in> \<lbrakk>G2\<rbrakk>"
  shows      "x \<in> \<lbrakk>G1\<rbrakk>"
proof-
  from e and b have 0: "\<exists> n. [NT S] -Rs2\<rightarrow>\<^sup>n x" (is "\<exists> n. ?P n")
    by (simp add: Lang_def Language_def Produces_def, auto)
  then obtain n where 1: "?P n" by blast
  from e have 2: "IsTerminalWord x"
    by (simp add: Lang_def Language_def Produces_def)
  from 1 and 2 and a and b and c show ?thesis
    by (induction n, auto, simp add: IsTerminalWord_def)
qed

theorem verifyTransformUnit :
  assumes a: "transformUnitSingle G1 A B G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0:  "\<exists>S Rs1 Rs2.
                  (S, Rs1) = G1 \<and>
                  (S, Rs2) = G2 \<and> 
                  (A, [NT B]) \<in> Rs1 \<and> 
                  Rs2 = Rs1 \<union> NewUnitTransRules A B Rs1 - {(A, [NT B])}"
                  (is "\<exists>S Rs1 Rs2. ?P S Rs1 Rs2")
    by (unfold transformUnitSingle_def, auto)
  then obtain S Rs1 Rs2 where 1: "?P S Rs1 Rs2" by blast
  from 1 have 2: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (meson Unit_Part1)
  from 1 have 3: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (meson Unit_Part2)
  from 2 and 3 show ?thesis
    by blast
qed

end
