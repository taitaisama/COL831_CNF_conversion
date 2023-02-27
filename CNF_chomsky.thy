theory CNF_chomsky
  imports Main
begin

section "Basic modelling"

datatype ('n, 't) Elem = NT "'n" | T "'t"
type_synonym ('n, 't) PartialEvaluation = "('n, 't) Elem list"
type_synonym ('n, 't) Rule = "'n \<times> ('n, 't) PartialEvaluation"
type_synonym ('n, 't) RuleSet = "('n, 't) Rule set"
type_synonym ('n, 't) CFG = "'n \<times> ('n, 't) RuleSet"

definition Productions :: "('n, 't)RuleSet \<Rightarrow> (('n, 't)PartialEvaluation \<times> ('n, 't)PartialEvaluation) set"
  where "Productions G = {(l @ [NT(N)] @ r, l @ rhs @ r) | l N r rhs. (N, rhs) \<in> G}"

definition ProductionStep :: "('n, 't) PartialEvaluation \<Rightarrow> ('n, 't)RuleSet \<Rightarrow> ('n, 't)PartialEvaluation \<Rightarrow> bool"  ("_ -_\<rightarrow> _" [60, 61, 60] 61) 
  where "w -G\<rightarrow> w' \<equiv> (w, w') \<in> Productions G"

fun ProducesInN :: "('n, 't) PartialEvaluation \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> nat \<Rightarrow> ('n, 't) PartialEvaluation \<Rightarrow> bool" ("_ -_\<rightarrow>\<^sup>_ _" [60, 61, 61, 60] 61)
  where "s -G\<rightarrow>\<^sup>0 t = (s = t)" | 
        "ProducesInN s G (Suc(n)) t = (\<exists> r. s -G\<rightarrow> r \<and> s -G\<rightarrow>\<^sup>n t)"

definition Produces :: "('n, 't) PartialEvaluation \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> ('n, 't) PartialEvaluation \<Rightarrow> bool" ("_ -_\<rightarrow>\<^sup>* _" [60, 61, 60] 61) 
  where "w -G\<rightarrow>\<^sup>* w' \<equiv> \<exists> n. w -G\<rightarrow>\<^sup>n w'"

definition IsTerminalWord :: "('n, 't) Elem list \<Rightarrow> bool"
  where "IsTerminalWord El \<equiv> \<not>(\<exists> a. NT(a) \<in> set El)"

definition Language :: "'n \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> (('n, 't) Elem list) set" ("\<lbrakk>_\<rbrakk>\<^sub>_" [60, 61])
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

definition NewUnitTransRuleSet :: "'n \<Rightarrow> 'n \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> ('n, 't) RuleSet"
  where "NewUnitTransRuleSet A B R1 \<equiv> {R2 | R2 Rhs. (B, Rhs) \<in> R1 \<and> (A, Rhs) = R2}"

definition transformUnitSingle :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformUnitSingle G1 A B G2 \<equiv> \<exists> S Rs1 Rs2. 
                                   (S, Rs1) = G1
                                   \<and> (S, Rs2) = G2
                                   \<and> (A, [NT(B)]) \<in> Rs1
                                   \<and> Rs2 = (Rs1 \<union> (NewUnitTransRuleSet A B Rs1)) - {(A, [NT(B)])}"

lemma Unit_Part1 :
  assumes a: "(S, Rs1) = G1"
  assumes b: "(S, Rs2) = G2"
  assumes c: "(A, [NT B]) \<in> Rs1"
  assumes d: "Rs2 = Rs1 \<union> NewUnitTransRuleSet A B Rs1 - {(A, [NT B])}"
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
  assumes d: "Rs2 = Rs1 \<union> NewUnitTransRuleSet A B Rs1 - {(A, [NT B])}"
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
                  Rs2 = Rs1 \<union> NewUnitTransRuleSet A B Rs1 - {(A, [NT B])}"
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

definition isNTToNTProduction :: "('n, 't) Rule \<Rightarrow> bool"
  where "isNTToNTProduction R \<equiv> \<exists> N1 N2. R = (N1, [NT N2])"

definition NTToNTProductionSet :: "('n, 't) RuleSet \<Rightarrow> ('n \<times> 'n) set"
  where "NTToNTProductionSet Rs \<equiv> {(N1, N2). (N1, [NT N2]) \<in> Rs}\<^sup>+"

definition NewUnitTransRuleSet2 :: "'n \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> ('n, 't) RuleSet"
  where "NewUnitTransRuleSet2 A R1 \<equiv> {R2 | B R2 Rhs. (B, Rhs) \<in> R1 
                                          \<and> (A, Rhs) = R2
                                          \<and> (A, B) \<in> NTToNTProductionSet R1
                                          \<and> \<not>isNTToNTProduction R2}"

definition NTToNTSetForA :: "'n \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> ('n, 't) RuleSet"
  where "NTToNTSetForA A R1 \<equiv> {R2 | R2 B. (A, [NT B]) = R2}"

definition transformUnitSingle2 :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformUnitSingle2 G1 A G2 \<equiv> \<exists> S Rs1 Rs2. 
                                   (S, Rs1) = G1
                                   \<and> (S, Rs2) = G2
                                   \<and> Rs2 = (Rs1 \<union> (NewUnitTransRuleSet2 A Rs1)) - (NTToNTSetForA A Rs1)"

lemma Unit2_Part1:
  assumes a: "(S, Rs1) = G1"
  assumes b: "(S, Rs2) = G2"
  assumes c: "Rs2 = Rs1 \<union>
       NewUnitTransRuleSet2 A Rs1 -
       NTToNTSetForA A Rs1"
  assumes d: "x \<in> \<lbrakk>G1\<rbrakk>"
  shows      "x \<in> \<lbrakk>G2\<rbrakk>"
proof-
  from a and d have 0: "\<exists> n. [NT S] -Rs1\<rightarrow>\<^sup>n x" (is "\<exists> n. ?P n")
    by (simp add: Lang_def Language_def Produces_def, auto)
  then obtain n where 1: "?P n" by blast
  from d have 2: "IsTerminalWord x"
    by (simp add: Lang_def Language_def Produces_def)
  from 1 and 2 and b and c show ?thesis
    by(simp add: NewUnitTransRuleSet2_def NTToNTProductionSet_def isNTToNTProduction_def NTToNTSetForA_def IsTerminalWord_def, induction n, auto)
qed


lemma Unit2_Part2:
  assumes a: "(S, Rs1) = G1"
  assumes b: "(S, Rs2) = G2"
  assumes c: "Rs2 = Rs1 \<union>
       NewUnitTransRuleSet2 A Rs1 -
       NTToNTSetForA A Rs1"
  assumes d: "x \<in> \<lbrakk>G2\<rbrakk>"
  shows      "x \<in> \<lbrakk>G1\<rbrakk>"
proof-
  from b and d have 0: "\<exists> n. [NT S] -Rs2\<rightarrow>\<^sup>n x" (is "\<exists> n. ?P n")
    by (simp add: Lang_def Language_def Produces_def, auto)
  then obtain n where 1: "?P n" by blast
  from d have 2: "IsTerminalWord x"
    by (simp add: Lang_def Language_def Produces_def)
  from 1 and 2 and a and c show ?thesis
    by(induction n, simp add: IsTerminalWord_def, auto)
qed

theorem verifyTransformUnit2 :
  assumes a: "transformUnitSingle2 G1 A G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0: "\<exists>S Rs1 Rs2.
       (S, Rs1) = G1 \<and>
       (S, Rs2) = G2 \<and>
       Rs2 =
       Rs1 \<union>
       NewUnitTransRuleSet2 A Rs1 -
       NTToNTSetForA A Rs1" (is "\<exists>S Rs1 Rs2. ?P S Rs1 Rs2")
    by (unfold transformUnitSingle2_def)
  then obtain S Rs1 Rs2 where 1: "?P S Rs1 Rs2" by blast
  from 1 have 2: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (meson Unit2_Part1)
  from 1 have 3: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (meson Unit2_Part2)
  from 2 and 3 show ?thesis
    by blast
qed
(*
type_synonym ('n, 't) Grammar = "'n \<times> ('n, 't) Rule list"
definition convCFG :: "('n, 't) Grammar \<Rightarrow> ('n, 't) CFG"
  where "convCFG G = (fst G, set (snd G))"

definition transTerm :: "('n, 't) Grammar \<Rightarrow> 'n \<Rightarrow> ('n, 't) Grammar \<Rightarrow> bool"
  where "transTerm G1 N G2 \<equiv> transformTermSingle (convCFG(G1)) N (convCFG(G2))" 

fun TerminalCount :: "('n, 't) Elem list \<Rightarrow> nat"
  where "TerminalCount Nil = 0" |
        "TerminalCount (T(a) # R) = 1 + TerminalCount R" |
        "TerminalCount (NT(a) # R) = TerminalCount R"

fun TerminalCountNonSingle :: "('n, 't) Elem list \<Rightarrow> nat"
  where "TerminalCountNonSingle ([T(a)]) = 0" |
        "TerminalCountNonSingle R = TerminalCount R"

fun MetricTerm1 :: "('n, 't) Rule list \<Rightarrow> nat"
  where "MetricTerm1 Nil = 0" |
        "MetricTerm1 ((_, R) # Rs) = (TerminalCountNonSingle R) + (MetricTerm1 Rs)"

fun MetricTerm :: "('n, 't) Grammar \<Rightarrow> nat"
  where "MetricTerm (S, R) = MetricTerm1 R"

theorem TerminationStart :
  assumes a: "transTerm G1 N G2"
  shows      "MetricTerm G1 > MetricTerm G2"
  using a apply-
  apply(simp add: transTerm_def transformTermSingle_def convCFG_def)
  sledgehammer  
*)

definition DelAllNullableNTsFromRules :: "('n, 't) RuleSet \<Rightarrow> ('n, 't) RuleSet"
  where "DelAllNullableNTsFromRules X = {R | R N. R \<in> DelNTFromRule N X \<and> Nil \<in> \<lbrakk>N\<rbrakk>\<^sub>X}"

definition RemoveAllEpsilonProds :: "'n \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> ('n, 't) RuleSet"
  where "RemoveAllEpsilonProds S X = {R | R N Rhs. R \<in> X \<and> (N, Rhs) = R \<and> (N = S \<or> Rhs \<noteq> Nil)}"

definition transformDel2 :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformDel2 G1 G2 \<equiv> \<exists> S Rs1 Rs2.
                                (S, Rs1) = G1
                                \<and> (S, Rs2) = G2
                                \<and> Rs2 = RemoveAllEpsilonProds S (Rs1 \<union> DelAllNullableNTsFromRules Rs1)"

lemma Del2_Part1:   
  assumes a: "(S, Rs1) = G1"
  assumes b: "(S, Rs2) = G2"
  assumes c: "Rs2 = RemoveAllEpsilonProds S (Rs1 \<union> DelAllNullableNTsFromRules Rs1)"
  assumes d: "x \<in> \<lbrakk>G1\<rbrakk>"
  shows      "x \<in> \<lbrakk>G2\<rbrakk>"
proof-
  from a and d have 0: "\<exists> n. [NT S] -Rs1\<rightarrow>\<^sup>n x" (is "\<exists> n. ?P n")
    by (simp add: Lang_def Language_def Produces_def, auto)
  then obtain n where 1: "?P n" by blast
  from d have 2: "IsTerminalWord x"
    by (simp add: Lang_def Language_def Produces_def)
  from 1 and 2 and b and c show ?thesis
    by(induction n, simp add: RemoveAllEpsilonProds_def DelAllNullableNTsFromRules_def DelNTFromRule_def DelNTFromRuleSet_def IsTerminalWord_def, auto)
qed

lemma Del2_Part2:   
  assumes a: "(S, Rs1) = G1"
  assumes b: "(S, Rs2) = G2"
  assumes c: "Rs2 = RemoveAllEpsilonProds S (Rs1 \<union> DelAllNullableNTsFromRules Rs1)"
  assumes d: "x \<in> \<lbrakk>G2\<rbrakk>"
  shows      "x \<in> \<lbrakk>G1\<rbrakk>"
proof-
  from b and d have 0: "\<exists> n. [NT S] -Rs2\<rightarrow>\<^sup>n x" (is "\<exists> n. ?P n")
    by (simp add: Lang_def Language_def Produces_def, auto)
  then obtain n where 1: "?P n" by blast
  from d have 2: "IsTerminalWord x"
    by (simp add: Lang_def Language_def Produces_def)
  from 1 and 2 and b and c show ?thesis
    by(induction n, simp add: RemoveAllEpsilonProds_def DelAllNullableNTsFromRules_def DelNTFromRule_def DelNTFromRuleSet_def IsTerminalWord_def, auto)
qed
  
theorem verifyTransformDel2: 
  assumes a: "transformDel2 G1 G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0:"\<exists> S Rs1 Rs2.
                 (S, Rs1) = G1
                 \<and> (S, Rs2) = G2
                 \<and> Rs2 = RemoveAllEpsilonProds S (Rs1 \<union> DelAllNullableNTsFromRules Rs1)"
                 (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
  by (unfold transformDel2_def)
  then obtain S Rs1 Rs2 where 1: "?P S Rs1 Rs2" by blast
  from 1 have 2: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (meson Del2_Part1)
  from 1 have 3: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (meson Del2_Part2)
  from 2 and 3 show ?thesis
    by blast
qed

definition finiteCFG :: "('n, 't) CFG \<Rightarrow> bool"
  where "finiteCFG G \<equiv> \<exists> S R. (S, R) = G \<and> finite R"

lemma StartFinite:
  assumes a: "transformStart G1 S0 G2"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG G2"
proof-
  from a and b show ?thesis
    by (metis Pair_inject finiteCFG_def finite_insert transformStart_def)
qed

lemma TermFinite:
  assumes a: "transformTermSingle G1 N G2"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG G2"
proof-
  from a and b show ?thesis
    by (unfold transformTermSingle_def finiteCFG_def, auto)
qed

lemma BinFinite:
  assumes a: "transformBinSingle G1 N G2"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG G2"
proof-
  from a and b show ?thesis
    by (unfold transformBinSingle_def finiteCFG_def, auto)
qed

lemma finiteImage:
  fixes  S1 :: "'a set"
  fixes  im :: "'a \<Rightarrow> 'b"
  assumes a : "finite S1"
  shows       "finite (image im S1)"
proof-
  from a show ?thesis by simp
qed

fun NTToNTRuleImg :: "('n, 't) Rule \<Rightarrow> 'n \<times>'n"
  where "NTToNTRuleImg (N1, [NT N2]) = (N1, N2)" | 
        "NTToNTRuleImg (S, R) = (S, S)"

lemma UnitFinit_part1:
  fixes   Rs1 :: "('n, 't) RuleSet"
  assumes a: "K = {R | R N1 N2. R \<in> Rs1 \<and> R = (N1, [NT N2])}"
  assumes b: "L = {(N1, N2) | R N1 N2. R \<in> Rs1 \<and> R = (N1, [NT N2])}"
  shows      "image NTToNTRuleImg K = L"
proof-
  from a and b show ?thesis
    by(auto, metis (mono_tags, lifting) CollectI NTToNTRuleImg.simps(1) image_eqI)
qed

lemma UnitFinit_part2:
  fixes      Rs1 :: "('n, 't) RuleSet"
  assumes a: "L = {(N1, N2) | R N1 N2. R \<in> Rs1 \<and> R = (N1, [NT N2])}"
  shows      "NTToNTProductionSet Rs1 = L\<^sup>+"
  using a apply-
  apply(unfold NTToNTProductionSet_def, auto)
  done

lemma UnitFinit_part3:
  fixes      Rs1 :: "('n, 't) RuleSet"
  assumes a: "finite Rs1"
  shows      "finite (NTToNTProductionSet Rs1)"
proof-
  from a have 0: "\<And>R. R \<subseteq> Rs1 \<Longrightarrow> finite R"
    by (simp add: finite_subset)
  have 1: "\<And>S. finite S \<Longrightarrow> finite (S\<^sup>+)"
    by simp
  from a and 0 have 3: "finite {R | R N1 N2. R \<in> Rs1 \<and> R = (N1, [NT N2])}"
    by auto
  from 3 and 0 and UnitFinit_part1 and UnitFinit_part2 show ?thesis
    by (smt (verit, del_insts) "1" Collect_cong finiteImage)
qed

definition CartesianProduct :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set"
  where "CartesianProduct A B = {(a, b). a \<in> A \<and> b \<in> B}"

lemma CartesianFinite:
  fixes      A :: "'a set"
  fixes      B :: "'b set"
  fixes      C :: "('a \<times> 'b) set"
  assumes a: "finite A"
  assumes b: "finite B"
  assumes c: "C = CartesianProduct A B "
  shows      "finite C"
proof-
  from a and b and c show ?thesis
    by (simp add :CartesianProduct_def)
qed

lemma UnitFinit_part4:
  fixes      A :: "('a \<times> 'b) set"
  fixes      B :: "('b \<times> 'c) set"
  fixes      C :: "('a \<times> 'c) set"
  assumes a: "finite A"
  assumes b: "finite B"
  assumes c: "C = {(a, c). \<exists> b. (a, b) \<in> A \<and> (b, c) \<in> B}"
  shows      "finite C"
proof-
  from a and b and c have 0: "C \<subseteq> CartesianProduct (image fst A) (image snd B)"
    by (smt (verit) CartesianProduct_def CollectI Product_Type.Collect_case_prodD fst_conv image_eqI snd_conv split_beta subsetI)
  from 0 and a and b and CartesianFinite and finiteImage show ?thesis
    by (metis finite_subset)
qed
    
lemma UnitFinit_part5:
  assumes a: "finite Rs1"
  shows      "finite (NewUnitTransRuleSet2 N Rs1)"
proof-
  from a and UnitFinit_part3 have 0: "finite (NTToNTProductionSet Rs1)"
    by (auto)
  from 0 and a and UnitFinit_part4 have 1: "finite {(A, Rhs). \<exists>B. (B, Rhs) \<in> Rs1 \<and> (A, B) \<in> (NTToNTProductionSet Rs1)}"
    by (smt (verit, del_insts) Collect_cong Pair_inject case_prodE case_prodI2)
  have 2: "NewUnitTransRuleSet2 N Rs1 \<subseteq> {(A, Rhs). \<exists>B. (B, Rhs) \<in> Rs1 \<and> (A, B) \<in> (NTToNTProductionSet Rs1)}"
    by (smt (verit, best) NewUnitTransRuleSet2_def Pair_inject case_prodI2 mem_Collect_eq subsetI)
  from 1 and 2 show ?thesis
    using finite_subset by blast
qed
  
lemma UnitFinite:
  assumes a: "transformUnitSingle2 G1 N G2"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG G2"
proof-
  from a and b and UnitFinit_part5 show ?thesis
    by (smt (verit) List.finite_set Pair_inject finiteCFG_def finite_Diff finite_distinct_list set_append transformUnitSingle2_def)
qed

(*
definition listSuffixSet :: "'a list \<Rightarrow> 'a list set"
  where "listSuffixSet R = {r. \<exists> l. R = l @ r}"

definition listPrefixSet :: "'a list \<Rightarrow> 'a list set"
  where "listPrefixSet R = {l. \<exists> r. R = l @ r}"

lemma listSuffixInduct:
  fixes      Rhs :: "'a list"
  shows      "listSuffixSet Rhs \<union> {a # Rhs} = listSuffixSet (a # Rhs) "
  apply (unfold listSuffixSet_def, induct Rhs, auto)
  apply (metis append_eq_Cons_conv append_is_Nil_conv)
  apply (meson Cons_eq_append_conv)
  done

lemma listSuffixFinite:
  fixes      Rhs :: "'a list"
  shows      "finite (listSuffixSet Rhs)"
  apply (unfold listSuffixSet_def, induct Rhs, auto)
  apply (metis List.finite_set finite_Un list.set(1) list.simps(15) listSuffixInduct listSuffixSet_def)
  done

lemma listPrefixInduct:
  fixes      Rhs :: "'a list"
  shows      "(image (Cons a) (listPrefixSet Rhs)) \<union> {Nil} = listPrefixSet (a # Rhs)"
  apply(unfold listPrefixSet_def, induction Rhs, auto)
  apply (simp add: Cons_eq_append_conv)
  apply (smt (verit, ccfv_threshold) Cons_eq_append_conv image_iff mem_Collect_eq)
  done

lemma listPrefixFinite:
  fixes      Rhs :: "'a list"
  shows      "finite (listPrefixSet Rhs)"
proof-
  from finiteImage have 0: "\<And>a Rhs.
       finite (listPrefixSet Rhs) \<Longrightarrow>
       finite ((image (Cons a) (listPrefixSet Rhs)) \<union> {Nil})"
    by blast
  from listPrefixInduct have 1: "\<And>a Rhs.
       finite ((image (Cons a) (listPrefixSet Rhs)) \<union> {Nil}) \<Longrightarrow>
       finite (listPrefixSet (a # Rhs))"
    by metis
  from 0 and 1 have 2: "\<And>a Rhs. finite (listPrefixSet Rhs) \<Longrightarrow> finite (listPrefixSet (a # Rhs))"
    by metis
  show ?thesis
    by(induction Rhs, unfold listPrefixSet_def, auto, fold listPrefixSet_def, simp add: 2)
qed

lemma DelFinite_Part1:
  fixes      Rhs :: "'a list"
  fixes      N :: "'a"
  fixes      S :: "('a list \<times> 'a list) set"
  assumes a: "S = {(l, r) | l r. Rhs = l @ (N # r)}"
  shows      "finite S"
proof-
  from a have 0: "S \<subseteq> CartesianProduct (listPrefixSet Rhs) (listSuffixSet Rhs)"
    by (unfold CartesianProduct_def listPrefixSet_def listSuffixSet_def, auto)
  from listPrefixFinite and listSuffixFinite and CartesianFinite and 0 show ?thesis
    by (metis finite_subset)
qed

fun DelFiniteConv :: "'n \<Rightarrow> (('n, 't) Elem list \<times> ('n, 't) Elem list) \<Rightarrow> ('n, 't) Rule"
  where "DelFiniteConv S (L, R) = (S, L @ R)"

lemma DelFinite_Part2:
  fixes      Rhs :: "('n, 't) Elem list"
  fixes      N :: "'n"
  fixes      S :: "'n"
  assumes a: "F = {w. \<exists>l r. w = (S, l @ r) \<and> Rhs = l @ ((NT N) # r)}"
  shows      "finite F"
proof-
  have 0: "\<And>x. x \<in> {(S, l @ r) |l r. Rhs = l @ NT N # r} \<Longrightarrow> 
           x \<in> image (DelFiniteConv S) {(l, r). Rhs = l @ ((NT N) # r)}"
    by force
  have 1: "\<And>x. x \<in> image (DelFiniteConv S) {(l, r). Rhs = l @ ((NT N) # r)} \<Longrightarrow>
           x \<in> {(S, l @ r) |l r. Rhs = l @ NT N # r}"
    by fastforce
  from 0 and 1 and a have 2: "F = image (DelFiniteConv S) {(l, r). Rhs = l @ ((NT N) # r)}"
    by blast
  have 3: "finite {(l, r). Rhs = l @ ((NT N) # r)}"
    by(rule_tac N="(NT N)" in DelFinite_Part1, auto)
  from 3 and 2 show ?thesis
    by (simp add: finiteImage)
qed

fun DelFiniteConv2 :: "'n \<Rightarrow> ('n, 't) Elem list \<Rightarrow> ('n, 't) Rule \<Rightarrow> (('n, 't) Rule \<times> ('n, 't) Rule )"
  where "DelFiniteConv2 S Rhs R = ((S, Rhs), R)"

lemma DelFinite_Part3:
  fixes      Rhs :: "('n, 't) Elem list"
  fixes      N :: "'n"
  fixes      S :: "'n"
  assumes a: "F = {((S, Rhs), w) | l r w. w = (S, l @ r) \<and> Rhs = l @ ((NT N) # r)}"
  shows      "finite F"
proof-
  from a have 0: "{((S, Rhs), w) | l r w. w = (S, l @ r) \<and> Rhs = l @ ((NT N) # r)} = image (DelFiniteConv2 S Rhs) 
                  {w. \<exists>l r. w = (S, l @ r) \<and> Rhs = l @ ((NT N) # r)}"
    by (auto)
  from 0 show ?thesis
    by (simp add: DelFinite_Part2 assms)
qed



lemma listFinite:
  fixes      L :: "'a list"
  shows      "finite (set L)"
  by auto

fun nthTransitive :: "nat \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
  where "nthTransitive 0 S = {}" |
        "nthTransitive (Suc N) S = {(a, b) | a b c. (a, b) \<in> S \<or> (a, c) \<in> S \<and> (b, c) \<in> (nthTransitive N S)}"

lemma transitivityMonotonic:
  fixes      L :: "('a \<times> 'a) set"
  fixes      f :: "'a \<Rightarrow> nat"
  assumes a: "\<And> A B. (A, B) \<in> L \<Longrightarrow> (f A) < (f B)"
  assumes c: "(A, B) \<in> (L\<^sup>+)"
  shows      "(f A) < (f B)"
  using a and c apply-
  apply(unfold trancl_def tranclp_def, auto)
  sledgehammer
*)

definition RuleRhsSize :: "('n, 't) Rule \<Rightarrow> nat"
  where "RuleRhsSize R \<equiv> size (snd R)"

lemma DelFinite_Part1:
  fixes      H :: "(('n, 't) Rule \<times> ('n, 't) Rule) set" 
  assumes a: "H = {((S, l @ r), S, l @ NT N # r) | S l r. True}"
  shows      "wf H"
proof-
  from a have 0: "\<And> A B. (A, B) \<in> H \<Longrightarrow> (RuleRhsSize A) < (RuleRhsSize B)"
    by (unfold RuleRhsSize_def, force)
  from 0 have 1: "H \<subseteq> (measure RuleRhsSize)"
    by fastforce
  from wf_measure have 2: "wf (measure RuleRhsSize)"
    by auto
  from 1 and 2 and wf_subset show ?thesis
    by blast
qed
    

lemma DelFinite_Part4:
  fixes      Rhs :: "('n, 't) Elem list"
  fixes      N :: "'n"
  fixes      S :: "'n"
  assumes a: "H = {NR | NR. ((S, Rhs), NR) \<in> DelNTFromRuleSet N}"
  shows      "(S, x) \<in> H \<Longrightarrow> (size x) < (size Rhs) \<or> (x = Rhs)"
proof-
  have 0:        "\<And>A B S. (A, B) \<in> S\<^sup>* \<Longrightarrow> A = B \<or> (A, B) \<in> S\<^sup>+"
    by (meson rtranclD)
  from 0 have 1: "\<And>S Rhs NR N. ((S, Rhs), NR) \<in> DelNTFromRuleSet N \<Longrightarrow> NR = (S, Rhs) 
           \<or> ((S, Rhs), NR) \<in> {((S, l @ NT N # r), S, l @ r) | S l r. True}\<^sup>+"
    by (unfold DelNTFromRuleSet_def, smt (verit) rtrancl_eq_or_trancl)
  have 2: "\<And> l r a. (size (l @ a # r)) > (size (l @ r))"
    by simp
  from 2 have 3: "\<And> S Rhs1 Rhs2 N. 
          ((S, Rhs1), (S, Rhs2)) \<in> {((S, l @ N # r), (S, l @ r)) | S l r. True} \<Longrightarrow>
          (size Rhs2) < (size Rhs1)"
    by force
  from 3 have 4: "\<And> Rhs1 Rhs2 N. 
          (Rhs1, Rhs2) \<in> {(l @ N # r, l @ r) | l r. True}\<^sup>+ \<Longrightarrow>
          (size Rhs2) < (size Rhs1)"
    sledgehammer
  
    
lemma DelFinite_Part5:
  fixes      Rhs :: "('n, 't) Elem list"
  fixes      N :: "'n"
  fixes      S :: "'n"
  assumes a: "H = {NR | NR. ((S, Rhs), NR) \<in> DelNTFromRuleSet N}"
  shows      "finite H"
proof-
  have 0:        "\<And>A B S. (A, B) \<in> S\<^sup>* \<Longrightarrow> A = B \<or> (A, B) \<in> S\<^sup>+"
    by (meson rtranclD)
  from a have 1: "\<And>A. A \<in> H \<Longrightarrow> ((S, Rhs), A) \<in> {((S, Rhs), (S, l @ r)) | S l r. Rhs = l @ ((NT N) # r)}\<^sup>*"
    sledgehammer
  from 0 and 1 have 2: "\<And>A. A \<in> H \<Longrightarrow> 
      ((S, Rhs), A) \<in> {((S, l @ ((NT N) # r)), (S, l @ r)) | S l r. True}\<^sup>+ \<or> A = (S, Rhs)"
    by (metis (no_types, lifting))
  from 2 have 3: "\<And>A. A \<in> H \<Longrightarrow> 
      ((S, Rhs), A) \<in> insert ((S, Rhs), (S, Rhs)) ({((S, l @ ((NT N) # r)), (S, l @ r)) | S l r. True}\<^sup>+)"
    by blast
  


lemma DelFinite_Part3:
  fixes      Rs1 :: "('n, 't) RuleSet"
  fixes      N :: "'n"
  assumes a: "finite Rs1"
  shows      "finite (DelNTFromRule N Rs1)"
  using a apply-
  apply(unfold DelNTFromRule_def)

lemma DelFinite_Part4:
  fixes      Rs1 :: "('n, 't) RuleSet"
  assumes a: "finite Rs1"
  shows      "finite (DelAllNullableNTsFromRules Rs1)"
  using a apply-
  apply (unfold DelAllNullableNTsFromRules_def)
  sledgehammer

lemma DelFinite:
  assumes a: "transformDel2 G1 G2"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG G2"
  using a and b apply-
  apply (unfold transformDel2_def)
  sledgehammer
end
