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

fun ProducesInN :: "('n, 't) PartialEvaluation \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> nat \<Rightarrow> ('n, 't) PartialEvaluation \<Rightarrow> bool" ("_ -_\<rightarrow>\<^sup>_ _" [60, 61, 1000, 60] 61)
  where "s -G\<rightarrow>\<^sup>0 t = (s = t)" | 
        "ProducesInN s G (Suc(n)) t = (\<exists> r. s -G\<rightarrow> r \<and> r -G\<rightarrow>\<^sup>n t)"

definition Produces :: "('n, 't) PartialEvaluation \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> ('n, 't) PartialEvaluation \<Rightarrow> bool" ("_ -_\<rightarrow>\<^sup>* _" [60, 61, 60] 61) 
  where "w -G\<rightarrow>\<^sup>* w' \<equiv> \<exists> n. w -G\<rightarrow>\<^sup>n w'"

definition ProductionRel :: "('n, 't) RuleSet \<Rightarrow> ('n, 't) PartialEvaluation \<Rightarrow>('n, 't) PartialEvaluation \<Rightarrow> bool"
  where "ProductionRel G w w' \<equiv> Produces w G w'"

definition IsTerminalWord :: "('n, 't) Elem list \<Rightarrow> bool"
  where "IsTerminalWord El \<equiv> \<not>(\<exists> a. NT(a) \<in> set El)"

definition PartialEvalLanguage :: "('n, 't) Elem list \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> (('n, 't) Elem list) set"
  where "PartialEvalLanguage E R = { w | w. IsTerminalWord w \<and> E -R\<rightarrow>\<^sup>* w}"

definition Language :: "'n \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> (('n, 't) Elem list) set" ("\<lbrakk>_\<rbrakk>\<^sub>_" [60, 61])
  where "\<lbrakk>S\<rbrakk>\<^sub>G = PartialEvalLanguage [NT S] G"

definition Lang :: "('n, 't) CFG \<Rightarrow> (('n, 't) Elem list) set" ("\<lbrakk>_\<rbrakk>")
  where "Lang G \<equiv> {w | w S R. w \<in> \<lbrakk>S\<rbrakk>\<^sub>R \<and> (S, R) = G}"

definition NTInRule :: "'n \<Rightarrow> ('n, 't) Rule \<Rightarrow> bool"
  where "NTInRule N R \<equiv> \<exists> S Rhs. (S, Rhs) = R \<and> (S = N \<or> (NT(N) \<in> set Rhs))"

definition NonTerminals :: "('n, 't) CFG \<Rightarrow> ('n, 't) Elem set"
  where "NonTerminals G = {NT(a) | S Rs a R. (S, Rs) = G \<and> (R \<in> Rs \<and> NTInRule a R \<or> S = a)}"

definition ProducingNT :: "('n, 't) Rule \<Rightarrow> 'n"
  where "ProducingNT R = fst R"

definition TInRule ::  "'t \<Rightarrow> ('n, 't) Rule \<Rightarrow> bool"
  where "TInRule N R \<equiv> \<exists> S Rhs. (S, Rhs) = R \<and> (T(N) \<in> set Rhs)"

definition Terminals :: "('n, 't) CFG \<Rightarrow> ('n, 't) Elem set"
  where "Terminals G = {T(a) | S Rs a R. (S, Rs) = G \<and> R \<in> Rs \<and> TInRule a R}"

section "Basic properties"

lemma productionSum:
  assumes a: "A -R\<rightarrow>\<^sup>n B"
  assumes b: "B -R\<rightarrow>\<^sup>m C"
  shows      "ProducesInN A R (n+m) C"
proof-
  have 0: "\<And> A B C m. A -R\<rightarrow>\<^sup>n B \<and> B -R\<rightarrow>\<^sup>m C \<Longrightarrow> ProducesInN A R (n+m) C"
    by(induction n, auto)
  from 0 show ?thesis 
    using a b by force
qed

lemma productionAppend1:
  assumes a: "N -R\<rightarrow> P"
  shows      "(l @ N @ r) -R\<rightarrow> (l @ P @ r)"
proof-
  from a show ?thesis
    apply(unfold ProductionStep_def Productions_def)
    by (smt (verit, best) Pair_inject append.assoc mem_Collect_eq)
qed

lemma productionAppend2:
  assumes a: "N -R\<rightarrow>\<^sup>n P"
  shows      "(l @ N @ r) -R\<rightarrow>\<^sup>n (l @ P @ r)"
proof-
  from productionAppend1 have 0: "\<And> N R P l r. ((N -R\<rightarrow>\<^sup>n P) \<Longrightarrow> (l @ N @ r) -R\<rightarrow>\<^sup>n (l @ P @ r))"
    by(induction n, auto, blast)
  from 0 show ?thesis
    using assms by blast
qed

lemma productionAppend3:
  assumes a: "N -R\<rightarrow>\<^sup>* P"
  shows      "(l @ N @ r) -R\<rightarrow>\<^sup>* (l @ P @ r)"
proof-
  from a have 0: "\<exists> n. N -R\<rightarrow>\<^sup>n P" (is "\<exists> n. ?P n")
    by (simp add: Produces_def)
  then obtain n where 1: "?P n" by blast
  from 1 and productionAppend2 show ?thesis
    apply(unfold Produces_def)
    by blast
qed

lemma transitiveProductions:
  assumes a: "a -R\<rightarrow>\<^sup>* b"
  assumes b: "b -R\<rightarrow>\<^sup>* c"
  shows      "a -R\<rightarrow>\<^sup>* c"
proof-  
  from a have 0: "\<exists> n. a -R\<rightarrow>\<^sup>n b" (is "\<exists> n. ?P n")
    by (simp add: Produces_def)
  then obtain n where 1: "?P n" by blast
  from b have 2: "\<exists> m. b -R\<rightarrow>\<^sup>m c" (is "\<exists> m. ?P m")
    by (simp add: Produces_def)
  then obtain m where 3: "?P m" by blast
  have 4: "\<And> a b. a -R\<rightarrow>\<^sup>n b \<and> b -R\<rightarrow>\<^sup>m c \<Longrightarrow> ProducesInN a R (n+m) c"
    by(induction n, auto)
  from 4 and 1 and 3 show ?thesis apply(unfold Produces_def) 
    by blast
qed

lemma transitiveClosureSame:
  fixes      R :: "('n, 't) RuleSet"
  assumes a: "(ProductionRel R)\<^sup>+\<^sup>+ a b"
  shows      "(ProductionRel R) a b"
proof-
  from a show ?thesis
    by(induction rule: tranclp_induct, unfold ProductionRel_def, auto, simp add: transitiveProductions)
qed

lemma transitiveSetToRel:
  fixes      f :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes      s :: "('a \<times> 'a) set"
  assumes a: "\<And> a b. (a, b) \<in> s \<Longrightarrow> f a b"
  assumes b: "(a, b) \<in> s\<^sup>+"
  shows      "f\<^sup>+\<^sup>+ a b"
proof-
  from a and b show ?thesis
    by (smt (verit, best) trancl_trans_induct tranclp.r_into_trancl tranclp_trans)
qed

lemma listPrefixSize:
  assumes a: "l @ r = a @ b"
  assumes b: "size l \<ge> size a"
  shows      "\<exists> c. l = a @ c"
proof-
  from a and b show ?thesis
    by (metis append_eq_append_conv_if append_eq_conv_conj)
qed

lemma listSuffixSize:
  assumes a: "l @ r = a @ b"
  assumes b: "size r \<ge> size b"
  shows      "\<exists> c. r = c @ b"
proof-
  from a and b show ?thesis
    by (smt (verit, ccfv_SIG) add_mono_thms_linordered_semiring(3) append_eq_append_conv append_eq_append_conv_if length_append verit_la_disequality)
qed

lemma productionParts1:
  assumes a: "l @ r -R\<rightarrow> X"
  shows      "(\<exists> l'. l -R\<rightarrow> l' \<and> l' @ r = X) \<or> (\<exists> r'. r -R\<rightarrow> r' \<and> l @ r' = X)"   
proof-
  from a have 0: "\<exists> N rhs a b. l @ r = (a @ [NT N] @ b) \<and> X = (a @ rhs @ b) \<and> (N, rhs) \<in> R" (is "\<exists> N rhs a b. ?P N rhs a b")
    by (smt (verit) Pair_inject ProductionStep_def Productions_def mem_Collect_eq)
  then obtain N rhs a b where 1: "?P N rhs a b" by blast
  from 1 have 3: "(size l \<ge> size (a @ [NT N])) \<Longrightarrow> \<exists> c. l = (a @ [NT N]) @ c"
    by (metis append.assoc listPrefixSize)
  have 4: "size l > size a \<Longrightarrow> size l \<ge> size (a @ [NT N])"
    by simp
  from 1 have 5: "size l + size r = size a + size ([NT N] @ b)"
    by (metis length_append)
  from 5 have 6: "size l \<le> size a \<Longrightarrow> size r \<ge> size ([NT N] @ b)"
    by linarith
  from 1 have 7: "size r \<ge> size ([NT N] @ b) \<Longrightarrow> \<exists> c. r = c @ ([NT N] @ b)"
    by (metis listSuffixSize)
  have 2: "((size l) > (size a)) \<or> ((size l) \<le> size a)"
    using linorder_not_less by blast
  then show ?thesis
  proof
    assume x: "(size l) > (size a)"
    from x and 4 have 8: "size l \<ge> size (a @ [NT N])"
      by auto
    from 8 and 3 have 9:"\<exists> c. l = (a @ [NT N]) @ c" (is "\<exists> c. ?P c")
      by auto
    then obtain c where 10: "?P c" by blast
    from 10 and 1 have 11: "l -R\<rightarrow> (a @ rhs @ c)"
      apply(unfold ProductionStep_def, auto) 
      using Productions_def by fastforce
    from 10 and 1 have 12: "c @ r = b" by simp
    from 1 and 12 and 11 have 13: "\<exists> l'. l -R\<rightarrow> l' \<and> l' @ r = X"
      by force
    show ?thesis
      by (simp add: "13")
  next
    assume y: "((size l) \<le> size a)"
    from y and 6 have 8: "size r \<ge> size ([NT N] @ b)"
      by auto
    from 8 and 7 have 9: "\<exists> c. r = c @ ([NT N] @ b)" (is "\<exists> c. ?P c")
      by auto
    then obtain c where 10: "?P c" by blast
    from 10 and 1 have 11: "r -R\<rightarrow> (c @ rhs @ b)"
      apply(unfold ProductionStep_def, auto) 
      using Productions_def by fastforce
    from 10 and 1 have 12: "l @ c = a" by simp
    from 1 and 12 and 11 have 13: "(\<exists> r'. r -R\<rightarrow> r' \<and> l @ r' = X)"
      by force
    show ?thesis
      by (simp add: "13")
  qed
qed  

lemma ProductionParts2:
  assumes a: "(\<And>X l r. l @ r -R\<rightarrow>\<^sup>n X \<Longrightarrow> \<exists>l' r'. l -R\<rightarrow>\<^sup>* l' \<and> r -R\<rightarrow>\<^sup>* r' \<and> l' @ r' = X)"
  assumes b: "ProducesInN (l@r) R (Suc(n)) X"
  shows      "\<exists>l' r'. l -R\<rightarrow>\<^sup>* l' \<and> r -R\<rightarrow>\<^sup>* r' \<and> l' @ r' = X"
proof-
  from b have 0: "\<exists> q. l@r -R\<rightarrow> q \<and> q -R\<rightarrow>\<^sup>n X" (is "\<exists> q. ?P q")
    by auto  
  then obtain q where 1 : "?P q" by blast
  from 1 and productionParts1 have 2:"(\<exists> l'. l -R\<rightarrow> l' \<and> l' @ r = q) \<or> (\<exists> r'. r -R\<rightarrow> r' \<and> l @ r' = q)"
    by metis
  have 3: "\<And> x. x -R\<rightarrow>\<^sup>0 x" 
    by simp
  from 3 have 4: "\<And> x. x -R\<rightarrow>\<^sup>* x" 
    using Produces_def by blast
  from 2 and 4 have 5: "\<exists> l' r'. q = l' @ r' \<and> l -R\<rightarrow>\<^sup>* l' \<and>  r -R\<rightarrow>\<^sup>* r'"
    by (meson ProducesInN.simps(1) ProducesInN.simps(2) Produces_def)
  from 5 and 1 show ?thesis
    by (smt (z3) "2" ProducesInN.simps(2) Produces_def a)
qed

lemma productionParts3:
  assumes a: "l @ r -R\<rightarrow>\<^sup>* X"
  shows      "\<exists> l' r'. l -R\<rightarrow>\<^sup>* l' \<and> r -R\<rightarrow>\<^sup>* r' \<and> l' @ r' = X"
proof-
  from a have 0: "\<exists> n. l @ r -R\<rightarrow>\<^sup>n X" (is "\<exists> n. ?P n")
    by (simp add: Produces_def)
  then obtain n where 1: "?P n" by blast
  have 2: "\<And> X l r. l @ r -R\<rightarrow>\<^sup>n X \<Longrightarrow> \<exists> l' r'. l -R\<rightarrow>\<^sup>* l' \<and> r -R\<rightarrow>\<^sup>* r' \<and> l' @ r' = X"
    apply(induction n)
    apply (meson ProducesInN.simps(1) Produces_def)
    using ProductionParts2 by blast
  from 2 and 1 show ?thesis
    by force
qed

lemma productionParts4:
  assumes a: "l -R\<rightarrow>\<^sup>* l'"
  assumes b: "r -R\<rightarrow>\<^sup>* r'"
  shows      "l @ r -R\<rightarrow>\<^sup>* l' @ r'"
proof-
  from a and productionAppend3 have 0: "l @ r -R\<rightarrow>\<^sup>* l' @ r"
    by (metis append_Nil)
  from b and productionAppend3 have 1: "l' @ r -R\<rightarrow>\<^sup>* l' @ r'"
    by (metis append.right_neutral)
  from 0 and 1 show ?thesis 
    using transitiveProductions by blast
qed

lemma productionParts5:
  assumes a: "\<And> l r X. l @ r -R\<rightarrow>\<^sup>n X \<Longrightarrow> \<exists>l' r' m. n \<ge> m \<and> l -R\<rightarrow>\<^sup>m l' \<and> ProducesInN r R (n-m) r' \<and> l' @ r' = X"
  assumes b: "ProducesInN (l @ r) R (n+1) X"
  shows      "\<exists>l' r' m. (n+1) \<ge> m \<and> l -R\<rightarrow>\<^sup>m l' \<and> ProducesInN r R ((n+1)-m) r' \<and> l' @ r' = X"
proof-
  from b have 0: "\<exists> t. (l @ r) -R\<rightarrow> t \<and> t -R\<rightarrow>\<^sup>n X" (is "\<exists> t. ?P t")
    by auto
  then obtain t where 1: "?P t" by blast
  from 1 and productionParts1 have 2: "(\<exists> l'. l -R\<rightarrow> l' \<and> l' @ r = t) \<or> (\<exists> r'. r -R\<rightarrow> r' \<and> l @ r' = t)"
    by blast
  then show ?thesis
  proof 
    assume "(\<exists> l1. l -R\<rightarrow> l1 \<and> l1 @ r = t)" (is "\<exists> l1. ?P l1")
    then obtain l1 where 3: "?P l1" by blast
    from 0 and 1 and a and 3 have 4: "\<exists>l' r' m. n \<ge> m \<and> l1 -R\<rightarrow>\<^sup>m l' \<and> ProducesInN r R (n-m) r' \<and> l' @ r' = X" (is "\<exists> l' r' m. ?P l' r' m")
      by simp
    then obtain l' r' m where 5: "?P l' r' m" by blast
    from 5 and 3 have 6: "ProducesInN l R (m+1) l'"
      by (metis ProducesInN.simps(2) Suc_eq_plus1)
    from 5 and 6 show ?thesis
      by(rule_tac x="l'" in exI, rule_tac x="r'" in exI, rule_tac x="m+1" in exI, auto)
  next
    assume "(\<exists> r1. r -R\<rightarrow> r1 \<and> l @ r1 = t)" (is "\<exists> r1. ?P r1")
    then obtain r1 where 3: "?P r1" by blast
    from 0 and 1 and a and 3 have 4: "\<exists>l' r' m. n \<ge> m \<and> l -R\<rightarrow>\<^sup>m l' \<and> ProducesInN r1 R (n-m) r' \<and> l' @ r' = X" (is "\<exists> l' r' m. ?P l' r' m")
      by simp
    then obtain l' r' m where 5: "?P l' r' m" by blast
    from 5 and 3 have 6: "ProducesInN r R (n-m+1) r'"
      by (metis ProducesInN.simps(2) Suc_eq_plus1)
    from 6 have 7:  "ProducesInN r R (n+1-m) r'"
      by (metis "5" Nat.add_diff_assoc2)
    from 5 and 7 show ?thesis
      by(rule_tac x="l'" in exI, rule_tac x="r'" in exI, rule_tac x="m" in exI, auto)
  qed
qed

lemma productionParts6:
  assumes a: "l @ r -R\<rightarrow>\<^sup>n X"
  shows      "\<exists> l' r' m. n \<ge> m \<and> l -R\<rightarrow>\<^sup>m l' \<and> ProducesInN r R (n-m) r' \<and> l' @ r' = X"
proof- 
  from productionParts5 have 0: "\<And>l r X n. ((\<And>l r X. l @ r -R\<rightarrow>\<^sup>n X \<Longrightarrow> 
           \<exists>l' r' m. m \<le> n \<and> l -R\<rightarrow>\<^sup>m l' \<and> ProducesInN r R (n-m) r' \<and> l' @ r' = X) \<Longrightarrow>
           (ProducesInN (l@r) R (n+1) X) \<Longrightarrow> 
            \<exists>l' r' m. m \<le> n + 1 \<and> l -R\<rightarrow>\<^sup>m l' \<and> (ProducesInN r R ((n+1)-m) r') \<and> l' @ r' = X)"
       by blast
  have 1: "\<And> l r X. l @ r -R\<rightarrow>\<^sup>n X \<Longrightarrow> \<exists> l' r' m. n \<ge> m \<and> l -R\<rightarrow>\<^sup>m l' \<and> ProducesInN r R (n-m) r' \<and> l' @ r' = X"
    apply(induction n) apply simp 
    using "0" by auto
  from 1 show ?thesis
    using assms by blast
qed

lemma productionParts7:
  assumes a: "l -R\<rightarrow>\<^sup>n l'"
  assumes b: "r -R\<rightarrow>\<^sup>m r'"
  shows      "ProducesInN (l @ r) R (n+m) (l' @ r')"
proof- 
  from a and productionAppend2 have 0: "ProducesInN (l @ r) R (n) (l' @ r)"
    by (metis append_Nil)
  from b have 1: "ProducesInN (l' @ r) R m (l' @ r')"
    by (metis append.right_neutral productionAppend2)
  from 0 and 1 and productionSum show ?thesis
    by blast
qed

lemma RuleSubset1:
  fixes      Rs1 :: "('n, 't) RuleSet"
  fixes      Rs2 :: "('n, 't) RuleSet"
  assumes a: "Rs1 \<subseteq> Rs2"
  assumes b: "S -Rs1\<rightarrow> X"
  shows      "S -Rs2\<rightarrow> X"
proof-
  from a and b show ?thesis
    by(unfold ProductionStep_def Productions_def, blast)
qed

lemma RuleSubset:
  fixes      Rs1 :: "('n, 't) RuleSet"
  fixes      Rs2 :: "('n, 't) RuleSet"  
  fixes      S :: "'n"
  assumes a: "Rs1 \<subseteq> Rs2"
  assumes b: "x \<in> Language S Rs1"
  shows      "x \<in> Language S Rs2"
proof-
  from b have 0: "\<exists>n. ([NT S]) -Rs1\<rightarrow>\<^sup>n x" (is "\<exists>n. ?P n")
    by(unfold Language_def PartialEvalLanguage_def Produces_def, auto)
  then obtain n where 1: "?P n" by blast
  from b have 2: "IsTerminalWord x"
    by (unfold Language_def PartialEvalLanguage_def Produces_def, auto)
  from a and RuleSubset1 have 3: "\<And> S x. S -Rs1\<rightarrow>\<^sup>n x \<Longrightarrow> S -Rs2\<rightarrow>\<^sup>n x"
    apply(induction n, auto, simp)
    by blast
  from 3 and 1 and 2 show ?thesis
    apply(unfold Language_def PartialEvalLanguage_def Produces_def, auto)
    done
qed

lemma OrderInvariant_Part1:
  fixes      Rs :: "('n, 't) RuleSet"
  fixes      P :: "('n, 't) Elem list"
  assumes a: "L = PartialEvalLanguage P Rs"
  assumes b: "P = l @ [NT N] @ r"
  assumes c: "Ls = {PartialEvalLanguage (l @ rhs @ r) Rs | rhs. (N, rhs) \<in> Rs}"
  assumes d: "x \<in> (\<Union> Ls)"
  shows      "x \<in> L"
proof-
  from c and d have 0: "\<exists> Rhs. (N, Rhs) \<in> Rs \<and> x \<in> PartialEvalLanguage (l @ Rhs @ r) Rs" (is "\<exists> Rhs. ?P Rhs")
    by blast
  then obtain Rhs where 1: "?P Rhs" by blast
  from 1 have 2: "(N, Rhs) \<in> Rs" by auto
  from 2 have 3: "[NT N] -Rs\<rightarrow> Rhs" 
    apply (simp add: ProductionStep_def Productions_def) 
    by fastforce
  from b and 3 and productionAppend1 have 4: "P -Rs\<rightarrow> (l @ Rhs @ r)" 
    by blast
  from 4 have 5: "PartialEvalLanguage (l @ Rhs @ r) Rs \<subseteq> PartialEvalLanguage P Rs"
    apply(unfold PartialEvalLanguage_def Produces_def)
    by (smt (verit) Collect_mono ProducesInN.simps(2))
  from a and b and c and d and 5 and 1 show ?thesis
    by blast
qed

lemma OrderInvariant_Part2:
  fixes      Rs :: "('n, 't) RuleSet"
  fixes      P :: "('n, 't) Elem list"
  assumes a: "L = PartialEvalLanguage P Rs"
  assumes b: "P = l @ [NT N] @ r"
  assumes c: "Ls = {PartialEvalLanguage (l @ rhs @ r) Rs | rhs. (N, rhs) \<in> Rs}"
  assumes d: "x \<in> L"
  shows      "x \<in> \<Union> Ls"
proof-
  from d and a have 0: "\<exists> n. P -Rs\<rightarrow>\<^sup>n x" (is "\<exists>n. ?P n")
    by(unfold PartialEvalLanguage_def Produces_def, auto)
  then obtain n where 1: "?P n" by blast
  from d and a have 2: "IsTerminalWord x"
    by(unfold PartialEvalLanguage_def Produces_def, auto)
  from b and a and d and productionParts3 have 3: "\<exists> ln r'. l @ [NT N] -Rs\<rightarrow>\<^sup>* ln \<and> r -Rs\<rightarrow>\<^sup>* r' \<and> x = ln@r'" (is "\<exists> ln r'. ?P ln r'")
    by (metis "0" Produces_def append_assoc)
  then obtain ln r' where 4: "?P ln r'" by blast
  from 4 have 5: "\<exists> l' rhs. l -Rs\<rightarrow>\<^sup>* l' \<and> [NT N]-Rs\<rightarrow>\<^sup>* rhs \<and> ln = l' @ rhs" (is "\<exists> l' rhs. ?P l' rhs")
    using productionParts3 by blast
  then obtain l' rhs where 6: "?P l' rhs" by blast
  from 4 and 6 have 7: "x = l' @ rhs @ r'" by auto
  from 6 have 8: "\<exists> k. [NT N] -Rs\<rightarrow>\<^sup>k rhs" (is "\<exists>k. ?P k") 
    by (unfold Produces_def, auto) 
  then obtain k where 9: "?P k" by blast
  from 9 and 2 have 10: "k \<ge> 1"
    using "7" IsTerminalWord_def in_set_conv_decomp not_less_eq_eq by fastforce
  from 10 and 8 have 11: "\<exists> rht. [NT N] -Rs\<rightarrow> rht \<and> ProducesInN rht Rs (k-1) rhs" (is "\<exists> rht. ?P rht")
    using "9" ProducesInN.elims(2) by fastforce
  then obtain rht where 12: "?P rht" by blast
  from 12 and 10 have 13: "rht -Rs\<rightarrow>\<^sup>* rhs"
    using Produces_def by blast 
  from 12 have 14: "l @ [NT N] @ r -Rs\<rightarrow> l @ rht @ r" 
    using productionAppend1 by blast
  from 13 have 15: "l @ rht @ r -Rs\<rightarrow>\<^sup>* l @ rhs @ r" 
    using productionAppend3 by blast
  from 15 and 13 and 4 and 6 have 16: "l @ rht @ r -Rs\<rightarrow>\<^sup>* l' @ rhs @ r'"
    by (simp add: productionParts4)
  from 16 and 7 have 17: "l @ rht @ r -Rs\<rightarrow>\<^sup>* x" by auto
  from 17 and 2 have 18: "x \<in> PartialEvalLanguage (l @ rht @ r) Rs" 
    using PartialEvalLanguage_def by blast
  from 12 have 19: "[NT N] -Rs\<rightarrow> rht" by auto
  from 19 have 20: "\<exists> lt rt rhst Nt. (lt @ [NT Nt] @ rt, lt @ rhst @ rt) = ([NT N], rht) \<and> (Nt, rhst) \<in> Rs" (is "\<exists> lt rt rhst Nt. ?P lt rt rhst Nt")
    apply(unfold ProductionStep_def Productions_def) 
    by fastforce
  then obtain lt rt rhst Nt where 21: "?P lt rt rhst Nt" by blast
  from 21 have 22: "lt = [] \<and> rt = [] \<and> N = Nt" 
    by (simp add: append_eq_Cons_conv)
  from 21 and 22 have 23: "rhst = rht" by auto
  from 21 and 22 and 23 have 24: "(N, rht) \<in> Rs" by auto
  from 12 and 24 have 25: "PartialEvalLanguage (l @ rht @ r) Rs \<in> Ls"
    using c by blast
  from 18 and 25 show ?thesis
    by blast
qed
  
lemma OrderInvariant:
  fixes      Rs :: "('n, 't) RuleSet"
  fixes      P :: "('n, 't) Elem list"
  fixes      l :: "('n, 't) Elem list"
  fixes      r :: "('n, 't) Elem list"
  fixes      L :: "('n, 't) Elem list set"
  fixes      Ls :: "('n, 't) Elem list set set"
  fixes      N :: "'n"
  assumes a: "L = PartialEvalLanguage P Rs"
  assumes b: "P = l @ [NT N] @ r"
  assumes c: "Ls = {PartialEvalLanguage (l @ rhs @ r) Rs | rhs. (N, rhs) \<in> Rs}"
  shows      "\<Union> Ls = L"
proof-
  from a and b and c and OrderInvariant_Part1 have 0: "\<And> x. (x \<in> \<Union> Ls \<Longrightarrow> x \<in> L)"
    by fastforce
  from a and b and c and OrderInvariant_Part2 have 1: "\<And> x. (x \<in> L \<Longrightarrow> x \<in> \<Union> Ls)"
    by fastforce
  from 0 and 1 show ?thesis by blast
qed  

lemma OrderInvStep: 
  fixes      Rs :: "('n, 't) RuleSet"
  fixes      P :: "('n, 't) Elem list"
  fixes      l :: "('n, 't) Elem list"
  fixes      r :: "('n, 't) Elem list"
  fixes      N :: "'n"
  fixes      n :: "nat"
  assumes a: "P = l @ [NT N] @ r"
  assumes b: "P -Rs\<rightarrow>\<^sup>n x"
  assumes c: "IsTerminalWord x"
  shows      "\<exists> rhs. (N, rhs) \<in> Rs \<and> ProducesInN (l @ rhs @ r) Rs (n-1) x" 
proof-
  from b and productionParts6 have 0: "\<exists> l' nr a. n \<ge> a \<and> l -Rs\<rightarrow>\<^sup>a l' \<and> ProducesInN ([NT N] @ r) Rs (n-a) nr \<and> l' @ nr = x"
    (is "\<exists> l' nr a. ?P l' nr a")
    using a by blast
  then obtain l' nr a where 1: "?P l' nr a" by blast
  from 1 have 2: "\<exists> N' r' b. n-a \<ge> b \<and> [NT N] -Rs\<rightarrow>\<^sup>b N' \<and> ProducesInN (r) Rs (n-a-b) r' \<and>  N' @ r' = nr"
    (is "\<exists> N' r' b. ?P N' r' b")
    by (meson diff_le_self le_trans productionParts6)
  then obtain N' r' b where 3: "?P N' r' b" by blast
  from c and 3 have 4: "N' \<noteq> [NT N]" 
    by (metis "1" IsTerminalWord_def append_Cons in_set_conv_decomp)
  from 4 and 3 and c have 5: "b \<ge> 1"
    by (metis One_nat_def ProducesInN.simps(1) Suc_leI bot_nat_0.not_eq_extremum)
  from 3 and 5 have 6: "\<exists> t. [NT N] -Rs\<rightarrow> t \<and> ProducesInN t Rs (b-1) N'" 
    (is "\<exists> t. ?P t")
    by (metis "4" ProducesInN.elims(2) diff_Suc_1)
  then obtain t where 7: "?P t" by blast
  from 7 and 3 and productionParts7 have 8: "ProducesInN (t @ r) Rs ((n-a-b)+(b-1)) nr"
    by (metis add.commute)
  from 8 and 1 and productionParts7 have 9: "ProducesInN (l @ t @ r) Rs ((n-a-b)+(b-1)+a) x"
    by (metis add.commute)
  from 1 and 3 have 10: "(n-a-b)+(b-1)+a = n-1"
    using "5" by force
  from 10 and 9 have 11: "ProducesInN (l @ t @ r) Rs (n-1) x" by auto
  from 7 have 12: "\<exists> ln rn Nn rhs. [NT N] = ln @ [NT Nn] @ rn \<and> t = ln @ rhs @ rn \<and> (Nn, rhs) \<in> Rs" (is "\<exists> ln rn Nn rhs. ?P  ln rn Nn rhs")
    apply(unfold ProductionStep_def Productions_def) 
    by blast
  then obtain ln rn Nn rhs where 13: "?P ln rn Nn rhs" by blast
  from 13 have 14: "ln = [] \<and> rn = [] \<and> Nn = N \<and> rhs = t"
    by (simp add: Cons_eq_append_conv)
  from 14 13 have 15: "(N, t) \<in> Rs" by auto
  from 11 and 15 show ?thesis by auto
qed

section "Transforms Definition"

definition transformStart :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool" 
  where "transformStart G1 S0 G2 \<equiv> \<exists> S1 R1 R2. (S1, R1) = G1 
                                   \<and> (S0, R2) = G2 
                                   \<and> NT(S0) \<notin> NonTerminals(G1)
                                   \<and> R2 = insert (S0, [NT(S1)]) R1"

lemma Start_Part1:
  assumes a: "G1 = (S1, R1)"
  assumes b: "G2 = (S0, R2)"
  assumes c: "NT(S0) \<notin> NonTerminals(G1)" 
  assumes d: "R2 = insert (S0, [NT S1]) R1"
  assumes e: "x \<in> \<lbrakk>G1\<rbrakk>"
  shows      "x \<in> \<lbrakk>G2\<rbrakk>"
proof-
  from e and a have 0: "IsTerminalWord x \<and> x \<in> Language S1 R1"
    apply(unfold Lang_def)
    by (simp add: Language_def PartialEvalLanguage_def)
  from 0 and a and c and b and d and RuleSubset have 1: "[NT S1] -R2\<rightarrow>\<^sup>* x" 
    by (metis (no_types, lifting) Language_def PartialEvalLanguage_def insertCI mem_Collect_eq subset_iff)
  from d have 2: "[NT S0] -R2\<rightarrow> [NT S1]"
    apply(unfold ProductionStep_def Productions_def)
    by fastforce
  from 2 and 1 show ?thesis 
    apply (simp add: Lang_def Language_def PartialEvalLanguage_def Produces_def)
    using "0" ProducesInN.simps(2) b by blast
qed 

lemma Start_Part2_induct1:
  assumes a: "G1 = (S1, R1)"
  assumes b: "G2 = (S0, R2)"
  assumes c: "NT(S0) \<notin> NonTerminals(G1)" 
  assumes d: "R2 = insert (S0, [NT S1]) R1"
  assumes e: "(\<And>A a. (NT S0 \<notin> set A) \<and> A -R2\<rightarrow>\<^sup>n a \<Longrightarrow> A -R1\<rightarrow>\<^sup>* a)"
  assumes f: "NT S0 \<notin> set A"
  assumes g: "ProducesInN A R2 (Suc n) a"
  shows      "A -R1\<rightarrow>\<^sup>* a"
proof-
  from a and c and b and d have 0: "\<And> R. R \<in> R2 \<Longrightarrow> R \<in> R1 \<or> R = (S0, [NT S1])"
    by blast
  from c have 1: "\<And> S1 Rhs1. (S1, Rhs1) \<in> R1 \<Longrightarrow> S0 \<noteq> S1 \<and> (NT S0) \<notin> set Rhs1"
    by (smt (verit, ccfv_threshold) CollectI NTInRule_def NonTerminals_def a)
  from 0 and 1 have 2: "\<And> Rhs. (S0, Rhs) \<in> R2 \<Longrightarrow> Rhs = [NT S1]"
    by blast
  from a and c and b and d and 2 have 3: "\<And> X. [NT S0] -R2\<rightarrow> X \<Longrightarrow> X = [NT S1]"
    apply(unfold ProductionStep_def Productions_def)
    by (smt (verit, best) Elem.inject(1) Pair_inject append_eq_Cons_conv append_is_Nil_conv list.discI list.inject mem_Collect_eq)
  from d and 2 have 4: "\<And> A B. A \<noteq> S0 \<and> (A, B) \<in> R2 \<Longrightarrow> (A, B) \<in> R1"
    by force
  from 4 have 5: "\<And> A B. A -R2\<rightarrow> B \<Longrightarrow> \<exists>l r N rhs. (l @ [NT N] @ r, l @ rhs @ r) = (A, B) \<and> (N, rhs) \<in> R2"
    by(unfold ProductionStep_def Productions_def, auto)
  from g have 6: "\<exists> t. A -R2\<rightarrow> t \<and> t -R2\<rightarrow>\<^sup>n a" (is "\<exists> t. ?P t")
    by simp
  then obtain t where 7: "?P t" by blast
  from 7 and 5 have 8: "\<exists>l r N rhs. (l @ [NT N] @ r, l @ rhs @ r) = (A, t) \<and> (N, rhs) \<in> R2" (is "\<exists> l r N rhs. ?P l r N rhs")
    by blast
  then obtain l r N rhs where 9: "?P l r N rhs" by blast
  from 9 and f have 10: "N \<noteq> S0" 
    by force
  from 10 and 4 have 11: "(N, rhs) \<in> R1" 
    using "9" by presburger
  from 11 and 9 have 12: "A -R1\<rightarrow> t" 
    using CollectI ProductionStep_def Productions_def by fastforce 
  from 12 and 7 and e and f have 13: "t -R1\<rightarrow>\<^sup>* a"
    by (smt (verit, ccfv_threshold) "11" "9" CollectI NTInRule_def NonTerminals_def Pair_inject Un_iff a c set_append)
  from 12 and 13 show ?thesis 
    by (meson ProducesInN.simps(2) Produces_def)
qed

lemma Start_Part2_induct2:
  assumes a: "G1 = (S1, R1)"
  assumes b: "G2 = (S0, R2)"
  assumes c: "NT(S0) \<notin> NonTerminals(G1)" 
  assumes d: "R2 = insert (S0, [NT S1]) R1"
  assumes f: "NT S0 \<notin> set A"
  assumes g: "(NT S0 \<notin> set A) \<and> A -R2\<rightarrow>\<^sup>n a"
  shows      "A -R1\<rightarrow>\<^sup>* a"
proof-
  from a and b and c and d have 0: "\<And> A a. (NT S0 \<notin> set A) \<and> A -R2\<rightarrow>\<^sup>n a \<Longrightarrow>  A -R1\<rightarrow>\<^sup>* a"
    apply(induction n)
    apply (metis ProducesInN.simps(1) Produces_def)
    by (metis Start_Part2_induct1 a c d)
  from 0 and g show ?thesis
    by blast
qed

lemma Start_Part2:
  assumes a: "G1 = (S1, R1)"
  assumes b: "G2 = (S0, R2)"
  assumes c: "NT(S0) \<notin> NonTerminals(G1)" 
  assumes d: "R2 = insert (S0, [NT S1]) R1"
  assumes e: "x \<in> \<lbrakk>G2\<rbrakk>"
  shows      "x \<in> \<lbrakk>G1\<rbrakk>"
proof-
  from e and b have 0: "IsTerminalWord x \<and> x \<in> Language S0 R2"
    apply(unfold Lang_def)
    by (simp add: Language_def PartialEvalLanguage_def)
  from 0 and b have 1: "\<exists> n. [NT S0] -R2\<rightarrow>\<^sup>n x" (is "\<exists>n. ?P n")
    by(unfold Lang_def Language_def PartialEvalLanguage_def Produces_def, auto)
  then obtain n where 2: "?P n" by blast
  from a and c and b and d have 3: "\<And> R. R \<in> R2 \<Longrightarrow> R \<in> R1 \<or> R = (S0, [NT S1])"
    by blast
  from c have 4: "\<And> S1 Rhs1. (S1, Rhs1) \<in> R1 \<Longrightarrow> S0 \<noteq> S1 \<and> (NT S0) \<notin> set Rhs1"
    by (smt (verit, ccfv_threshold) CollectI NTInRule_def NonTerminals_def a)
  from 3 and 4 have 5: "\<And> Rhs. (S0, Rhs) \<in> R2 \<Longrightarrow> Rhs = [NT S1]"
    by blast
  from a and c and b and d and 5 have 6: "\<And> X. [NT S0] -R2\<rightarrow> X \<Longrightarrow> X = [NT S1]"
    apply(unfold ProductionStep_def Productions_def)
    by (smt (verit, best) Elem.inject(1) Pair_inject append_eq_Cons_conv append_is_Nil_conv list.discI list.inject mem_Collect_eq) 
  have 7: "\<And> A a m. (NT S0 \<notin> set A) \<and> A -R2\<rightarrow>\<^sup>m a \<Longrightarrow>  A -R1\<rightarrow>\<^sup>* a"
    by (metis Start_Part2_induct2 a c d)
  from 6 and 0 and 1 have 8: "\<exists> r. [NT S0] -R2\<rightarrow> r \<and> ProducesInN r R2 (n-1) x"
    by (metis "2" IsTerminalWord_def ProducesInN.elims(2) diff_Suc_1 list.set_intros(1))
  from 8 and 6 and 7 have 9: "[NT S0] -R2\<rightarrow> [NT S1] \<and> ProducesInN [NT S1] R2 (n-1) x"
    by force
  from c have 10: "S1 \<noteq> S0"
    by (simp add: NonTerminals_def a)
  from 10 have 11: "(NT S0) \<notin> set [NT S1]"
    by auto
  from 9 and 7 and 11 have 12: "[NT S1] -R2\<rightarrow>\<^sup>* x"
    using Produces_def by blast
  from 12 show ?thesis 
    by (metis (mono_tags, lifting) "0" "11" "7" "9" CollectI Lang_def Language_def PartialEvalLanguage_def a)
qed

theorem verifyTransformStart:
  assumes a: "transformStart G1 S0 G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 1: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (metis Start_Part1 transformStart_def)  
  from a have 2: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (metis Start_Part2 transformStart_def)
  from 1 and 2 show ?thesis
    by blast
qed

definition transformTermSingle :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformTermSingle G1 N G2 \<equiv> \<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
                                 (S, Rs1) = G1 
                                 \<and> R1 = (S1, L @ (T(a) # R))
                                 \<and> R2 = (S1, L @ (NT(N) # R))
                                 \<and> R3 = (N, [T a])
                                 \<and> (L @ R \<noteq> [])
                                 \<and> (S, Rs2) = G2 
                                 \<and> R1 \<in> Rs1
                                 \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                                 \<and> NT(N) \<notin> NonTerminals(G1)"

lemma Term_Part1_induct1:
  assumes p: "transformTermSingle G1 N G2"
  assumes g: "(NT N) \<notin> set A"
  assumes l: "\<And>A x. ((NT N) \<notin> set A \<and> A -(snd G1)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G2)\<rightarrow>\<^sup>* x)"
  assumes m: "ProducesInN A (snd G1) (Suc n) x"
  shows      "A -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from p have q: "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
                  (S, Rs1) = G1 
                  \<and> R1 = (S1, L @ (T(a) # R))
                  \<and> R2 = (S1, L @ (NT(N) # R))
                  \<and> R3 = (N, [T a])
                  \<and> (L @ R \<noteq> [])
                  \<and> (S, Rs2) = G2 
                  \<and> R1 \<in> Rs1
                  \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                  \<and> NT(N) \<notin> NonTerminals(G1)"
          (is "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. ?P S R1 R2 R3 Rs1 Rs2 S1 L R a")
    by (simp add: transformTermSingle_def)
  then obtain S R1 R2 R3 Rs1 Rs2 S1 L R a where r: "?P S R1 R2 R3 Rs1 Rs2 S1 L R a" by blast
  from r have a: "R1 = (S1, L @ T a # R)" by auto
  from r have b: "R2 = (S1, L @ NT N # R)" by auto
  from r have c: "R3 = (N, [T a])" by auto
  from r have d: "(L @ R \<noteq> [])" by auto
  from r have e: "G1 = (S, Rs1)" by auto
  from r have f: "G2 = (S, Rs2)" by auto
  from r have i: "R1 \<in> Rs1" by auto
  from r have j: "Rs2 = {R2, R3} \<union> (Rs1 - {R1})" by auto
  from r have k: "NT N \<notin> NonTerminals G1" by auto
  from m and e have 0: "\<exists> t. A -Rs1\<rightarrow> t \<and> t -Rs1\<rightarrow>\<^sup>n x" (is "\<exists> t. ?P t")
    by simp
  then obtain t where 1: "?P t" by blast
  from j have 00: "\<And> T. T \<in> Rs1 \<Longrightarrow> T = R1 \<or> T \<in> Rs2"
    by blast
  from a and 00 have 2: "\<And> A B. (A, B) \<in> Rs1 \<Longrightarrow> (A = S1 \<and> B = L @ T a # R) \<or> (A, B) \<in> Rs2"
    by blast
  show ?thesis
proof cases
  assume x: "\<exists> l r. A = l @ [NT S1] @ r \<and> t = l @ L @ T a # R @ r" (is "\<exists> l r. ?P l r")
  then obtain l r where 3: "?P l r" by blast
  from b and j and x and 3 have 4: "A -Rs2\<rightarrow> l @ L @ NT N # R @ r"
    apply(unfold ProductionStep_def Productions_def)
    by (smt (verit, ccfv_threshold) Cons_eq_appendI Un_commute Un_insert_right append_assoc insert_iff mem_Collect_eq)
  from c and j and x have 5: "(N, [T a]) \<in> Rs2"
    by blast
  from 5 and 3 have 6: "l @ L @ NT N # R @ r -Rs2\<rightarrow> t"
    apply(unfold ProductionStep_def Productions_def) 
    by (smt (verit, del_insts) Cons_eq_appendI append_Nil append_assoc mem_Collect_eq)
  from 6 and 4 have 7: "A -Rs2\<rightarrow>\<^sup>* t" 
    by (meson ProducesInN.simps(1) ProducesInN.simps(2) Produces_def)
  from k and a and i have 8: "(NT N) \<notin> set (L @ T a # R)"
    apply(unfold NonTerminals_def)
    using NTInRule_def e by fastforce
  from g and 3 have 9: "(NT N) \<notin> set l \<and> (NT N) \<notin> set r"
    by simp
  from 8 and 9 and 3 have 10: "(NT N) \<notin> set t"
    by simp
  from 10 and l and 7 and 1 and e and f transitiveProductions show ?thesis  
    by (metis snd_conv)
next
  assume y: "\<not> (\<exists> l r. A = l @ [NT S1] @ r \<and> t = l @ L @ T a # R @ r)"
  from 1 have 3: "\<exists> l r P Rhs. A =  l @ [NT P] @ r \<and> t = l @ Rhs @ r \<and> (P, Rhs) \<in> Rs1" (is "\<exists>  l r P Rhs. ?P l r P Rhs")
    by (smt (verit, ccfv_SIG) Pair_inject ProductionStep_def Productions_def mem_Collect_eq)
  then obtain l r P Rhs where 4: "?P l r P Rhs" by blast
  from 2 and 4 and y have 5: "(P, Rhs) \<in> Rs2"
    by fastforce
  from 5 have 6: "A -Rs2\<rightarrow> t" 
    using "4" CollectI ProductionStep_def Productions_def by fastforce
  from k and a and i and 3 have 8: "(NT N) \<notin> set Rhs"
    apply(unfold NonTerminals_def)
    using "4" NTInRule_def e by force
  from g and 4 have 9: "(NT N) \<notin> set l \<and> (NT N) \<notin> set r"
    by simp
  from 8 and 9 and 4 have 10: "(NT N) \<notin> set t"
    by simp
  from 6 have 11: "A -Rs2\<rightarrow>\<^sup>* t" 
    by (meson ProducesInN.simps(1) ProducesInN.simps(2) Produces_def)
  from 1 and 10 and l and 11 and e and f and transitiveProductions show ?thesis
    by fastforce
  qed  
qed

lemma Term_Part1_induct2:
  fixes      A :: "('n, 't) Elem list"
  fixes      G1 :: "('n, 't) CFG"
  assumes p: "transformTermSingle G1 N G2"
  assumes l: "(NT N) \<notin> set A" 
  assumes m: "A -(snd G1)\<rightarrow>\<^sup>n x"
  shows      "A -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from p and l and Term_Part1_induct1 have 0: "\<And>A x. (NT N \<notin> set A \<and> A -snd G1\<rightarrow>\<^sup>n x \<Longrightarrow> A -snd G2\<rightarrow>\<^sup>* x)"
    apply (induction n)
    apply (metis ProducesInN.simps(1) Produces_def)
    by (smt (verit) Term_Part1_induct1)
  from 0 and m and l show ?thesis
    by blast
qed
  
lemma Term_Part1:
  assumes a: "transformTermSingle G1 N G2"
  assumes b: "x \<in> \<lbrakk>G1\<rbrakk>"
  shows      "x \<in> \<lbrakk>G2\<rbrakk>"
proof-
  from b have 0: "\<exists> n S Rs1. [NT S] -Rs1\<rightarrow>\<^sup>n x \<and> (S, Rs1) = G1" (is "\<exists> n S Rs1. ?P n S Rs1")
    by (simp add: Language_def Lang_def Produces_def PartialEvalLanguage_def, auto)
  then obtain n S Rs1 where 1: "?P n S Rs1" by blast
  from Term_Part1_induct2 and a have 2: "\<And>A B x n. ((NT N) \<notin> set A \<and> A -(snd G1)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G2)\<rightarrow>\<^sup>* x)"
    by metis
  from a have 3: "NT N \<notin> NonTerminals G1"
    by(unfold transformTermSingle_def, auto)
  from 1 and 3 have 4: "N \<noteq> S"
    by(unfold NonTerminals_def, auto)
  from 4 have 5: "NT N \<notin> set ([NT S])"
    by simp
  from 5 and 2 and 1 have 6: "[NT S] -(snd G2)\<rightarrow>\<^sup>* x"
    by force
  from a and 1 have 7: "\<exists> Rs2. G2 = (S, Rs2)" (is "\<exists> Rs2. ?P Rs2")
    by(unfold transformTermSingle_def, blast)
  then obtain Rs2 where 8: "?P Rs2" by blast
  from b have 9: "IsTerminalWord x" 
    by (unfold Lang_def Language_def PartialEvalLanguage_def, auto)
  from 8 and 6 and 9 show ?thesis
    by (unfold Lang_def Language_def PartialEvalLanguage_def, auto)
qed

lemma Term_Part2_induct1:
  assumes a: "transformTermSingle G1 N G2"
  assumes b: "(NT N) \<notin> set A"
  assumes c: "\<And>m A x. (m \<le> n \<and> IsTerminalWord x \<and> (NT N) \<notin> set A \<and> A -(snd G2)\<rightarrow>\<^sup>m x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
  assumes d: "ProducesInN A (snd G2) (Suc n) x"
  assumes p: "IsTerminalWord x"
  shows      "A -(snd G1)\<rightarrow>\<^sup>* x"
proof-
  from a have 0: "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
                  (S, Rs1) = G1 
                  \<and> R1 = (S1, L @ (T(a) # R))
                  \<and> R2 = (S1, L @ (NT(N) # R))
                  \<and> R3 = (N, [T a])
                  \<and> (L @ R \<noteq> [])
                  \<and> (S, Rs2) = G2 
                  \<and> R1 \<in> Rs1
                  \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                  \<and> NT(N) \<notin> NonTerminals(G1)"
          (is "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. ?P S R1 R2 R3 Rs1 Rs2 S1 L R a")
    by (simp add: transformTermSingle_def)
  then obtain S R1 R2 R3 Rs1 Rs2 S1 L R a where 1: "?P S R1 R2 R3 Rs1 Rs2 S1 L R a" by blast
  from 1 have e: "R1 = (S1, L @ T a # R)" by auto
  from 1 have f: "R2 = (S1, L @ NT N # R)" by auto
  from 1 have g: "R3 = (N, [T a])" by auto
  from 1 have h: "(L @ R \<noteq> [])" by auto
  from 1 have i: "G1 = (S, Rs1)" by auto
  from 1 have j: "G2 = (S, Rs2)" by auto
  from 1 have k: "R1 \<in> Rs1" by auto
  from 1 have l: "Rs2 = {R2, R3} \<union> (Rs1 - {R1})" by auto
  from 1 have m: "NT N \<notin> NonTerminals G1" by auto
  from d and j have 0: "\<exists> t. A -Rs2\<rightarrow> t \<and> t -Rs2\<rightarrow>\<^sup>n x" (is "\<exists> t. ?P t")
    by simp
  then obtain t where 2: "?P t" by blast
  from l have 3: "\<And> T. T \<in> Rs2 \<Longrightarrow> (T = R2 \<or> T = R3) \<or> T \<in> Rs1" (* r2 is fine, r3 isn't *)
    by blast
  from f have 4: "(NT N) \<in> (set (snd R2))"
    by auto
  from 2 have 5: "\<exists> l r rhs N'. A = l @ [NT N'] @ r \<and> t = l @ rhs @ r \<and> (N', rhs) \<in> Rs2"
    (is "\<exists> l r rhs N'. ?P l r rhs N'")
    by (unfold ProductionStep_def Productions_def, auto) 
  then obtain l r rhs N' where 6: "?P l r rhs N'" by blast
  from 3 and 6 have 7: "(N', rhs) = R2 \<or> (N', rhs) = R3 \<or> (N', rhs) \<in> Rs1"
    by auto
  from 6 and g and 3 and b have 8: "(N', rhs) \<noteq> R3" 
    by auto
  from 8 and 7 have 9: "(N', rhs) = R2 \<or> (N', rhs) \<in> Rs1"
    by auto
  then show ?thesis
proof 
  assume x: "(N', rhs) = R2"
  from f and x and 6 have 10: "t = l @ L @ [NT N] @ R @ r" by auto
  from 10 and 2 and p and OrderInvStep have 11: "\<exists>rhs1. (N, rhs1) \<in> Rs2 \<and> ProducesInN (l @ L @ rhs1 @ R @ r) Rs2 (n-1) x"
    (is "\<exists> rhs1. ?P rhs1")
    by (metis append.assoc)
  then obtain rhs1 where 12: "?P rhs1" by blast
  from m and i have 13: "\<And> rhs. (N, rhs) \<notin> Rs1"
    by(unfold NonTerminals_def NTInRule_def, blast)
  from 3 and 12 and 13 and f and g have 14: "(N, rhs1) = R3"
    using "1" by blast
  from 14 and g have 15: "rhs1 = [T a]" by auto
  from m and k and e have 16: "(NT N) \<notin> set L \<and> (NT N) \<notin> set R"
    by (smt (verit, ccfv_threshold) "1" NTInRule_def NonTerminals_def Un_iff insert_iff list.simps(15) mem_Collect_eq set_append)
  from b and 6 have 17: "(NT N) \<notin> set l \<and> (NT N) \<notin> set r"
    by simp
  from 16 and 17 and 15 have 18: "(NT N) \<notin> set (l @ L @ rhs1 @ R @ r)"
    by simp
  from c and 18 and 12 have 19: "(l @ L @ rhs1 @ R @ r) -Rs1\<rightarrow>\<^sup>* x"
    by (metis "1" diff_le_self p snd_conv)
  from e and k have 20: "l @ [NT S1] @ r -Rs1\<rightarrow> l @ L @ [T a] @ R @ r"
    apply(unfold ProductionStep_def Productions_def)
    by fastforce
  from x and 6 and 15 and 20 and f have 21: "A -Rs1\<rightarrow> l @ L @ rhs1 @ R @ r"
    by force
  from 21 and 19 show ?thesis
    by (metis ProducesInN.simps(2) Produces_def i snd_conv)
next
  assume x: "(N', rhs) \<in> Rs1"
  from x and 6 have 10: "A -Rs1\<rightarrow> t"
    apply(unfold ProductionStep_def Productions_def)
    by blast
  from m and k and e have 11: "(NT N) \<notin> set L \<and> (NT N) \<notin> set R"
    by (smt (verit, ccfv_threshold) "1" NTInRule_def NonTerminals_def Un_iff insert_iff list.simps(15) mem_Collect_eq set_append)
  from b and 6 have 12: "(NT N) \<notin> set l \<and> (NT N) \<notin> set r"
    by simp
  from x and m have 13: "(NT N) \<notin> set rhs"
    by (smt (verit) "1" CollectI NTInRule_def NonTerminals_def)
  from 13 and 12 and 6 have 14: "(NT N) \<notin> set t"
    by auto
  from 14 and 2 and c have 15: "t -Rs1\<rightarrow>\<^sup>* x"
    using i j p by auto
  from 15 and 10 show ?thesis
    by (metis ProducesInN.simps(2) Produces_def i snd_eqD)
  qed
qed

lemma Term_Part2_induct2:
  assumes a: "transformTermSingle G1 N G2"
  assumes b: "(NT N) \<notin> set A"
  assumes c: "\<And>m A x. (m < n \<and> IsTerminalWord x \<and> (NT N) \<notin> set A \<and> A -(snd G2)\<rightarrow>\<^sup>m x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
  assumes d: "ProducesInN A (snd G2) n x"
  assumes p: "IsTerminalWord x"
  shows      "A -(snd G1)\<rightarrow>\<^sup>* x"
proof-
  have "n > 0 \<or> n = 0" by auto
  then show ?thesis
  proof
    assume x: "n > 0"
    from x have 0: "\<exists> n'. n' = n-1" (is "\<exists> n'. ?P n'") by auto
    then obtain n' where 1: "?P n'" by blast
    from 1 and c have 2: "\<And>m A x. (m \<le> n' \<and> IsTerminalWord x \<and> (NT N) \<notin> set A \<and> A -(snd G2)\<rightarrow>\<^sup>m x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
      by (metis Suc_pred' less_Suc_eq_le x)
    from 1 and d have 3: "ProducesInN A (snd G2) (Suc n') x"
      by (simp add: x)
    from 2 and 3 and p and a and b and Term_Part2_induct1 show ?thesis
      by (metis (no_types, lifting))      
  next
    assume y: "n = 0"
    from d and y have 0: "x = A"
      by simp
    from 0 show ?thesis
      by (meson ProducesInN.simps(1) Produces_def)
  qed
qed

lemma Term_Part2_induct3:
  fixes      A :: "('n, 't) Elem list"
  fixes      G1 :: "('n, 't) CFG"
  assumes p: "transformTermSingle G1 N G2"
  assumes l: "(NT N) \<notin> set A" 
  assumes k: "IsTerminalWord x"
  assumes m: "A -(snd G2)\<rightarrow>\<^sup>n x"
  shows      "A -(snd G1)\<rightarrow>\<^sup>* x"
proof-
  have 0: "\<And>A x. IsTerminalWord x \<and> (NT N) \<notin> set A \<and> A -(snd G2)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x"
    apply (induction n rule: less_induct)
    by (smt (verit, best) Term_Part2_induct2 p)
  from 0 and p and l and m and k show ?thesis 
    by simp
qed

lemma Term_Part2:
  assumes a: "transformTermSingle G1 N G2"
  assumes b: "x \<in> \<lbrakk>G2\<rbrakk>"
  shows      "x \<in> \<lbrakk>G1\<rbrakk>"
proof-
  from b have 0: "\<exists> n S Rs2. [NT S] -Rs2\<rightarrow>\<^sup>n x \<and> (S, Rs2) = G2" (is "\<exists> n S Rs2. ?P n S Rs2")
    by (simp add: Language_def Lang_def Produces_def PartialEvalLanguage_def, auto)
  then obtain n S Rs2 where 1: "?P n S Rs2" by blast
  from Term_Part2_induct3 and a have 2: "\<And>A B x n. ((NT N) \<notin> set A \<and> IsTerminalWord x \<and> A -(snd G2)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
    by metis
  from a have 3: "NT N \<notin> NonTerminals G1"
    by(unfold transformTermSingle_def, auto)
  from a and 1 and 3 have 4: "N \<noteq> S"
    by (unfold NonTerminals_def transformTermSingle_def, auto)
  from 4 have 5: "NT N \<notin> set ([NT S])"
    by simp
  from b have 6: "IsTerminalWord x"
    by (simp add: Lang_def Language_def PartialEvalLanguage_def)
  from 5 and 2 and 1 and 6 have 7: "[NT S] -(snd G1)\<rightarrow>\<^sup>* x"
    by force
  from a and 1 have 8: "\<exists> Rs1. G1 = (S, Rs1)" (is "\<exists> Rs1. ?P Rs1")
    by(unfold transformTermSingle_def, auto)
  then obtain Rs1 where 9: "?P Rs1" by blast
  from 9 and 7 and 6 show ?thesis
    by(unfold Lang_def Language_def PartialEvalLanguage_def, auto)
qed

theorem verifyTransformTerm: 
  assumes a: "transformTermSingle G1 N G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (simp add: Term_Part1)
  from a have 1: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (simp add: Term_Part2)
  from 0 and 1 show ?thesis
    by fastforce
qed

definition transformBinSingle :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformBinSingle G1 N G2 \<equiv> \<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
                                   (S, Rs1) = G1 
                                 \<and> R1 = (S1, L @ a # R)
                                 \<and> R2 = (S1, L @ [NT N])
                                 \<and> R3 = (N, a # R)  
                                 \<and> L \<noteq> [] \<and> R \<noteq> []
                                 \<and> (S, Rs2) = G2 
                                 \<and> R1 \<in> Rs1
                                 \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                                 \<and> NT(N) \<notin> NonTerminals(G1)"

lemma Bin_Part1_induct1:
  assumes p: "transformBinSingle G1 N G2"
  assumes g: "(NT N) \<notin> set A"
  assumes l: "\<And>A x. ((NT N) \<notin> set A \<and> A -(snd G1)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G2)\<rightarrow>\<^sup>* x)"
  assumes m: "ProducesInN A (snd G1) (Suc n) x"
  shows      "A -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from p have q: "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
                  (S, Rs1) = G1 
                  \<and> R1 = (S1, L @ a # R)
                  \<and> R2 = (S1, L @ [NT N])
                  \<and> R3 = (N, a # R)  
                  \<and> L \<noteq> [] \<and> R \<noteq> []
                  \<and> (S, Rs2) = G2 
                  \<and> R1 \<in> Rs1
                  \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                  \<and> NT(N) \<notin> NonTerminals(G1)"
          (is "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. ?P S R1 R2 R3 Rs1 Rs2 S1 L R a")
    by (simp add: transformBinSingle_def)
  then obtain S R1 R2 R3 Rs1 Rs2 S1 L R a where r: "?P S R1 R2 R3 Rs1 Rs2 S1 L R a" by blast
  from r have a: "R1 = (S1, L @ a # R)" by auto
  from r have b: "R2 = (S1, L @ [NT N])" by auto
  from r have c: "R3 = (N, a # R)" by auto
  from r have d: "L \<noteq> [] \<and> R \<noteq> []" by auto
  from r have e: "G1 = (S, Rs1)" by auto
  from r have f: "G2 = (S, Rs2)" by auto
  from r have i: "R1 \<in> Rs1" by auto
  from r have j: "Rs2 = {R2, R3} \<union> (Rs1 - {R1})" by auto
  from r have k: "NT N \<notin> NonTerminals G1" by auto
  from m and e have 0: "\<exists> t. A -Rs1\<rightarrow> t \<and> t -Rs1\<rightarrow>\<^sup>n x" (is "\<exists> t. ?P t")
    by simp
  then obtain t where 1: "?P t" by blast
  from j have 00: "\<And> T. T \<in> Rs1 \<Longrightarrow> T = R1 \<or> T \<in> Rs2"
    by blast
  from a and 00 have 2: "\<And> A B. (A, B) \<in> Rs1 \<Longrightarrow> (A = S1 \<and> B = L @ a # R) \<or> (A, B) \<in> Rs2"
    by blast
  from 1 have 3: "\<exists> l r rhs N'. A = l @ [NT N'] @ r \<and> t = l @ rhs @ r \<and> (N', rhs) \<in> Rs1"
    (is "\<exists> l r rhs N'. ?P l r rhs N'")
    by (unfold ProductionStep_def Productions_def, auto) 
  then obtain l r rhs N' where 4: "?P l r rhs N'" by blast
  from k and 4 and e have 10: "NT N \<notin> set rhs"
    using NTInRule_def NonTerminals_def by force
  from 10 and g and 4 have 11: "NT N \<notin> set t"
    by simp
  from 2 and 4 have 5: "(N' = S1 \<and> rhs = L @ a # R) \<or> (N', rhs) \<in> Rs2"
    by auto
  then show ?thesis
  proof 
    assume x: "(N' = S1 \<and> rhs = L @ a # R)"
    from c have 6: "L @ [NT N] -Rs2\<rightarrow> L @ a # R"
      apply (unfold ProductionStep_def Productions_def)
      using r by fastforce
    from b have 7: "[NT S1] -Rs2\<rightarrow> L @ [NT N]"
      apply (unfold ProductionStep_def Productions_def)
      using r by fastforce
    from 6 and 7 have 8: "[NT S1] -Rs2\<rightarrow>\<^sup>* L @ a # R"
      by (meson ProducesInN.simps(1) ProducesInN.simps(2) Produces_def)
    from 8 have 9: "A -Rs2\<rightarrow>\<^sup>* t"
      using "4" productionAppend3 x by blast
    from 9 and 1 and l and 11 show ?thesis
      using e f transitiveProductions by fastforce
  next
    assume y: "(N', rhs) \<in> Rs2"
    from y and 4 have 6: "A -Rs2\<rightarrow> t"
      using ProductionStep_def Productions_def by fastforce
    from 6 and 1 and l and 11 show ?thesis
      by (metis ProducesInN.simps(2) Produces_def e f snd_conv)
  qed
qed


lemma Bin_Part1_induct2:
  fixes      A :: "('n, 't) Elem list"
  fixes      G1 :: "('n, 't) CFG"
  assumes p: "transformBinSingle G1 N G2"
  assumes l: "(NT N) \<notin> set A" 
  assumes m: "A -(snd G1)\<rightarrow>\<^sup>n x"
  shows      "A -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from p and l and Bin_Part1_induct1 have 0: "\<And>A x. (NT N \<notin> set A \<and> A -snd G1\<rightarrow>\<^sup>n x \<Longrightarrow> A -snd G2\<rightarrow>\<^sup>* x)"
    apply (induction n)
    apply (metis ProducesInN.simps(1) Produces_def)
    by (smt (verit) Bin_Part1_induct1)
  from 0 and m and l show ?thesis
    by blast
qed

lemma Bin_Part1:
  assumes a: "transformBinSingle G1 N G2"
  assumes b: "x \<in> \<lbrakk>G1\<rbrakk>"
  shows      "x \<in> \<lbrakk>G2\<rbrakk>"
proof-
  from b have 0: "\<exists> n S Rs1. [NT S] -Rs1\<rightarrow>\<^sup>n x \<and> (S, Rs1) = G1" (is "\<exists> n S Rs1. ?P n S Rs1")
    by (simp add: Language_def Lang_def Produces_def PartialEvalLanguage_def, auto)
  then obtain n S Rs1 where 1: "?P n S Rs1" by blast
  from Bin_Part1_induct2 and a have 2: "\<And>A B x n. ((NT N) \<notin> set A \<and> A -(snd G1)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G2)\<rightarrow>\<^sup>* x)"
    by metis
  from a have 3: "NT N \<notin> NonTerminals G1"
    by(unfold transformBinSingle_def, auto)
  from 1 and 3 have 4: "N \<noteq> S"
    by(unfold NonTerminals_def, auto)
  from 4 have 5: "NT N \<notin> set ([NT S])"
    by simp
  from 5 and 2 and 1 have 6: "[NT S] -(snd G2)\<rightarrow>\<^sup>* x"
    by force
  from a and 1 have 7: "\<exists> Rs2. G2 = (S, Rs2)" (is "\<exists> Rs2. ?P Rs2")
    by(unfold transformBinSingle_def, blast)
  then obtain Rs2 where 8: "?P Rs2" by blast
  from b have 9: "IsTerminalWord x" 
    by (unfold Lang_def Language_def PartialEvalLanguage_def, auto)
  from 8 and 6 and 9 show ?thesis
    by (unfold Lang_def Language_def PartialEvalLanguage_def, auto)
qed

lemma Bin_Part2_induct1:
  assumes a: "transformBinSingle G1 N G2"
  assumes b: "(NT N) \<notin> set A"
  assumes c: "\<And>m A x. (m \<le> n \<and> IsTerminalWord x \<and> (NT N) \<notin> set A \<and> A -(snd G2)\<rightarrow>\<^sup>m x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
  assumes d: "ProducesInN A (snd G2) (Suc n) x"
  assumes p: "IsTerminalWord x"
  shows      "A -(snd G1)\<rightarrow>\<^sup>* x"
proof-
  from a have 0: "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
                  (S, Rs1) = G1 
                  \<and> R1 = (S1, L @ a # R)
                  \<and> R2 = (S1, L @ [NT N])
                  \<and> R3 = (N, a # R)  
                  \<and> L \<noteq> [] \<and> R \<noteq> []
                  \<and> (S, Rs2) = G2 
                  \<and> R1 \<in> Rs1
                  \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                  \<and> NT(N) \<notin> NonTerminals(G1)"
          (is "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. ?P S R1 R2 R3 Rs1 Rs2 S1 L R a")
    by (simp add: transformBinSingle_def)
  then obtain S R1 R2 R3 Rs1 Rs2 S1 L R a where 1: "?P S R1 R2 R3 Rs1 Rs2 S1 L R a" by blast
  from 1 have e: "R1 = (S1, L @ a # R)" by auto
  from 1 have f: "R2 = (S1, L @ [NT N])" by auto
  from 1 have g: "R3 = (N, a # R)" by auto
  from 1 have h: "L \<noteq> [] \<and> R \<noteq> []" by auto
  from 1 have i: "G1 = (S, Rs1)" by auto
  from 1 have j: "G2 = (S, Rs2)" by auto
  from 1 have k: "R1 \<in> Rs1" by auto
  from 1 have l: "Rs2 = {R2, R3} \<union> (Rs1 - {R1})" by auto
  from 1 have m: "NT N \<notin> NonTerminals G1" by auto
  from d and j have 0: "\<exists> t. A -Rs2\<rightarrow> t \<and> t -Rs2\<rightarrow>\<^sup>n x" (is "\<exists> t. ?P t")
    by simp
  then obtain t where 2: "?P t" by blast
  from l have 3: "\<And> T. T \<in> Rs2 \<Longrightarrow> (T = R2 \<or> T = R3) \<or> T \<in> Rs1" (* r2 is fine, r3 isn't *)
    by blast
  from f have 4: "(NT N) \<in> (set (snd R2))"
    by auto
  from 2 have 5: "\<exists> l r rhs N'. A = l @ [NT N'] @ r \<and> t = l @ rhs @ r \<and> (N', rhs) \<in> Rs2"
    (is "\<exists> l r rhs N'. ?P l r rhs N'")
    by (unfold ProductionStep_def Productions_def, auto) 
  then obtain l r rhs N' where 6: "?P l r rhs N'" by blast
  from 3 and 6 have 7: "(N', rhs) = R2 \<or> (N', rhs) = R3 \<or> (N', rhs) \<in> Rs1"
    by auto
  from 6 and g and 3 and b have 8: "(N', rhs) \<noteq> R3" 
    by auto
  from 8 and 7 have 9: "(N', rhs) = R2 \<or> (N', rhs) \<in> Rs1"
    by auto
  then show ?thesis
proof 
  assume x: "(N', rhs) = R2"
  from f and x and 6 have 10: "t = l @ L @ [NT N] @ r" by auto
  from 10 and 2 and p and OrderInvStep have 11: "\<exists>rhs1. (N, rhs1) \<in> Rs2 \<and> ProducesInN (l @ L @ rhs1 @ r) Rs2 (n-1) x"
    (is "\<exists> rhs1. ?P rhs1")
    by (metis append.assoc)
  then obtain rhs1 where 12: "?P rhs1" by blast
  from m and i have 13: "\<And> rhs. (N, rhs) \<notin> Rs1"
    by(unfold NonTerminals_def NTInRule_def, blast)
  from 3 and 12 and 13 and f and g have 14: "(N, rhs1) = R3"
    using "1" by blast
  from 14 and g have 15: "rhs1 = a # R" by auto
  from m and k and e have 16: "(NT N) \<notin> set L \<and> (NT N) \<notin> set rhs1"
    by (smt (verit, ccfv_threshold) "1" "15" CollectI NTInRule_def NonTerminals_def Un_iff set_append)
  from b and 6 have 17: "(NT N) \<notin> set l \<and> (NT N) \<notin> set r"
    by simp
  from 16 and 17 and 15 have 18: "(NT N) \<notin> set (l @ L @ rhs1 @ r)"
    by simp
  from c and 18 and 12 have 19: "(l @ L @ rhs1 @ r) -Rs1\<rightarrow>\<^sup>* x"
    by (metis "1" diff_le_self p snd_conv)
  from e and k have 20: "l @ [NT S1] @ r -Rs1\<rightarrow> l @ L @ a # R @ r"
    apply(unfold ProductionStep_def Productions_def)
    by fastforce
  from x and 6 and 15 and 20 and f have 21: "A -Rs1\<rightarrow> l @ L @ rhs1  @ r"
    by force
  from 21 and 19 show ?thesis
    by (metis ProducesInN.simps(2) Produces_def i snd_conv)
next
  assume x: "(N', rhs) \<in> Rs1"
  from x and 6 have 10: "A -Rs1\<rightarrow> t"
    apply(unfold ProductionStep_def Productions_def)
    by blast
  from m and k and e have 11: "(NT N) \<notin> set L \<and> (NT N) \<notin> set R"
    by (smt (verit, ccfv_threshold) "1" NTInRule_def NonTerminals_def Un_iff insert_iff list.simps(15) mem_Collect_eq set_append)
  from b and 6 have 12: "(NT N) \<notin> set l \<and> (NT N) \<notin> set r"
    by simp
  from x and m have 13: "(NT N) \<notin> set rhs"
    by (smt (verit) "1" CollectI NTInRule_def NonTerminals_def)
  from 13 and 12 and 6 have 14: "(NT N) \<notin> set t"
    by auto
  from 14 and 2 and c have 15: "t -Rs1\<rightarrow>\<^sup>* x"
    using i j p by auto
  from 15 and 10 show ?thesis
    by (metis ProducesInN.simps(2) Produces_def i snd_eqD)
  qed
qed

lemma Bin_Part2_induct2:
  assumes a: "transformBinSingle G1 N G2"
  assumes b: "(NT N) \<notin> set A"
  assumes c: "\<And>m A x. (m < n \<and> IsTerminalWord x \<and> (NT N) \<notin> set A \<and> A -(snd G2)\<rightarrow>\<^sup>m x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
  assumes d: "ProducesInN A (snd G2) n x"
  assumes p: "IsTerminalWord x"
  shows      "A -(snd G1)\<rightarrow>\<^sup>* x"
proof-
  have "n > 0 \<or> n = 0" by auto
  then show ?thesis
  proof
    assume x: "n > 0"
    from x have 0: "\<exists> n'. n' = n-1" (is "\<exists> n'. ?P n'") by auto
    then obtain n' where 1: "?P n'" by blast
    from 1 and c have 2: "\<And>m A x. (m \<le> n' \<and> IsTerminalWord x \<and> (NT N) \<notin> set A \<and> A -(snd G2)\<rightarrow>\<^sup>m x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
      by (metis Suc_pred' less_Suc_eq_le x)
    from 1 and d have 3: "ProducesInN A (snd G2) (Suc n') x"
      by (simp add: x)
    from 2 and 3 and p and a and b and Bin_Part2_induct1 show ?thesis
      by (metis (no_types, lifting))      
  next
    assume y: "n = 0"
    from d and y have 0: "x = A"
      by simp
    from 0 show ?thesis
      by (meson ProducesInN.simps(1) Produces_def)
  qed
qed

lemma Bin_Part2_induct3:
  fixes      A :: "('n, 't) Elem list"
  fixes      G1 :: "('n, 't) CFG"
  assumes p: "transformBinSingle G1 N G2"
  assumes l: "(NT N) \<notin> set A" 
  assumes k: "IsTerminalWord x"
  assumes m: "A -(snd G2)\<rightarrow>\<^sup>n x"
  shows      "A -(snd G1)\<rightarrow>\<^sup>* x"
proof-
  have 0: "\<And>A x. IsTerminalWord x \<and> (NT N) \<notin> set A \<and> A -(snd G2)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x"
    apply (induction n rule: less_induct)
    by (smt (verit, best) Bin_Part2_induct2 p)
  from 0 and p and l and m and k show ?thesis 
    by simp
qed

lemma Bin_Part2:
  assumes a: "transformBinSingle G1 N G2"
  assumes b: "x \<in> \<lbrakk>G2\<rbrakk>"
  shows      "x \<in> \<lbrakk>G1\<rbrakk>"
proof-
  from b have 0: "\<exists> n S Rs2. [NT S] -Rs2\<rightarrow>\<^sup>n x \<and> (S, Rs2) = G2" (is "\<exists> n S Rs2. ?P n S Rs2")
    by (simp add: Language_def Lang_def Produces_def PartialEvalLanguage_def, auto)
  then obtain n S Rs2 where 1: "?P n S Rs2" by blast
  from Bin_Part2_induct3 and a have 2: "\<And>A B x n. ((NT N) \<notin> set A \<and> IsTerminalWord x \<and> A -(snd G2)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
    by metis
  from a have 3: "NT N \<notin> NonTerminals G1"
    by(unfold transformBinSingle_def, auto)
  from a and 1 and 3 have 4: "N \<noteq> S"
    by (unfold NonTerminals_def transformBinSingle_def, auto)
  from 4 have 5: "NT N \<notin> set ([NT S])"
    by simp
  from b have 6: "IsTerminalWord x"
    by (simp add: Lang_def Language_def PartialEvalLanguage_def)
  from 5 and 2 and 1 and 6 have 7: "[NT S] -(snd G1)\<rightarrow>\<^sup>* x"
    by force
  from a and 1 have 8: "\<exists> Rs1. G1 = (S, Rs1)" (is "\<exists> Rs1. ?P Rs1")
    by(unfold transformBinSingle_def, auto)
  then obtain Rs1 where 9: "?P Rs1" by blast
  from 9 and 7 and 6 show ?thesis
    by(unfold Lang_def Language_def PartialEvalLanguage_def, auto)
qed

theorem verifyTransformBin: 
  assumes a: "transformBinSingle G1 N G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (simp add: Bin_Part1)
  from a have 1: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (simp add: Bin_Part2)
  from 0 and 1 show ?thesis
    by fastforce
qed


(* This definition doesn't terminate *)
(*
definition transformDelSingle :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformDelSingle G1 N G2 \<equiv> \<exists> S Rs1 Rs2. 
                                N \<noteq> S 
                                \<and> (S, Rs1) = G1
                                \<and> (S, Rs2) = G2
                                \<and> (N, Nil) \<in> Rs1
                                \<and> Rs2 = (DelNTFromRule N Rs1) - {(N, Nil)}"

definition NewUnitTransRuleSet :: "'n \<Rightarrow> 'n \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> ('n, 't) RuleSet"
  where "NewUnitTransRuleSet A B R1 \<equiv> {R2 | R2 Rhs. (B, Rhs) \<in> R1 \<and> (A, Rhs) = R2}"

definition transformUnitSingle :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformUnitSingle G1 A B G2 \<equiv> \<exists> S Rs1 Rs2. 
                                   (S, Rs1) = G1
                                   \<and> (S, Rs2) = G2
                                   \<and> (A, [NT(B)]) \<in> Rs1
                                   \<and> Rs2 = (Rs1 \<union> (NewUnitTransRuleSet A B Rs1)) - {(A, [NT(B)])}"
*)

definition isNTToNTProduction :: "('n, 't) Rule \<Rightarrow> bool"
  where "isNTToNTProduction R \<equiv> \<exists> N1 N2. R = (N1, [NT N2])"

definition NTToNTProductionSet :: "('n, 't) RuleSet \<Rightarrow> ('n \<times> 'n) set"
  where "NTToNTProductionSet Rs \<equiv> {(N1, N2). (N1, [NT N2]) \<in> Rs}\<^sup>+"

definition NewUnitTransRuleSet :: "'n \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> ('n, 't) RuleSet"
  where "NewUnitTransRuleSet A R1 \<equiv> {R2 | B R2 Rhs. (B, Rhs) \<in> R1 
                                          \<and> (A, Rhs) = R2
                                          \<and> (A, B) \<in> NTToNTProductionSet R1
                                          \<and> \<not>isNTToNTProduction R2}"

definition NTToNTSetForA :: "'n \<Rightarrow> ('n, 't) RuleSet"
  where "NTToNTSetForA A \<equiv> {R2 | R2 B. (A, [NT B]) = R2}"

definition transformUnitSingle :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformUnitSingle G1 A G2 \<equiv> \<exists> S Rs1 Rs2. 
                                   (S, Rs1) = G1
                                   \<and> (S, Rs2) = G2
                                   \<and> Rs2 = (Rs1 \<union> (NewUnitTransRuleSet A Rs1)) - (NTToNTSetForA A)"

lemma Unit_Part1:
  fixes      Rs :: "('n, 't) RuleSet"
  assumes a: "(N1, N2) \<in> NTToNTProductionSet Rs"
  shows      "[NT N1] -Rs\<rightarrow>\<^sup>* [NT N2]"
proof-
  have 0: "\<And> a b. (a, [NT b]) \<in> Rs \<Longrightarrow> [NT a] -Rs\<rightarrow> [NT b]"
    by(unfold ProductionStep_def Productions_def, fastforce) 
  from 0 have 1: "\<And> a b. (a, [NT b]) \<in> Rs \<Longrightarrow> [NT a] -Rs\<rightarrow>\<^sup>* [NT b]"
    by (meson ProducesInN.simps(1) ProducesInN.simps(2) Produces_def)
  from 1 have 2: "\<And> a b. (a, b) \<in> {(N1, N2). (N1, [NT N2]) \<in> Rs} \<Longrightarrow> [NT a] -Rs\<rightarrow>\<^sup>* [NT b]"
    by blast
  from 2 have 3: "\<And> a b. (a, b) \<in> {(N1, N2). (N1, [NT N2]) \<in> Rs} \<Longrightarrow> (\<lambda> a b. (ProductionRel Rs) [NT a] [NT b]) a b"
    by (auto, unfold ProductionRel_def)
  from 3 and transitiveSetToRel have 4: "\<And> a b. (a, b) \<in> {(N1, N2). (N1, [NT N2]) \<in> Rs}\<^sup>+ \<Longrightarrow> (\<lambda> a b. (ProductionRel Rs) [NT a] [NT b])\<^sup>+\<^sup>+ a b"
    by (metis (no_types, lifting))
  from 4 have 5: "\<And> a b. (a, b) \<in> {(N1, N2). (N1, [NT N2]) \<in> Rs}\<^sup>+ \<Longrightarrow> (ProductionRel Rs)\<^sup>+\<^sup>+ [NT a] [NT b]"
    by (smt (verit, del_insts) ProductionRel_def tranclp.r_into_trancl tranclp_trans_induct transitiveProductions)
  from 5 have 6: "\<And> a b. (a, b) \<in> {(N1, N2). (N1, [NT N2]) \<in> Rs}\<^sup>+ \<Longrightarrow> (ProductionRel Rs) [NT a] [NT b]"
    using transitiveClosureSame by blast
  from 6  and a have 7: "\<And> a b. (a, b) \<in> NTToNTProductionSet Rs \<Longrightarrow> [NT a] -Rs\<rightarrow>\<^sup>* [NT b]"
    by (simp add: ProductionRel_def NTToNTProductionSet_def)
  from a and 7 show ?thesis
    by auto
qed

lemma Unit_Part2:
  fixes      Rs :: "('n, 't) RuleSet"
  assumes a: "(A, Rhs) \<in> NewUnitTransRuleSet A Rs"
  shows      "[NT A] -Rs\<rightarrow>\<^sup>* Rhs"
proof-
  from a have 0:  "\<exists>B. (B, Rhs) \<in> Rs \<and> (A, B) \<in> NTToNTProductionSet Rs" (is "\<exists>B. ?P B")
    by (unfold NewUnitTransRuleSet_def, auto)
  then obtain B where 1: "?P B" by blast
  from 1 have 2: "[NT B] -Rs\<rightarrow> Rhs"
    by (unfold ProductionStep_def Productions_def, fastforce)
  from 1 have 3: "[NT A] -Rs\<rightarrow>\<^sup>* [NT B]"
    by (simp add: Unit_Part1)
  from 2 and 3 show ?thesis
    by (metis ProducesInN.elims(3) ProducesInN.simps(2) Produces_def nat.simps(3) transitiveProductions)
qed

definition UnitInductionStep :: "('n, 't) RuleSet \<Rightarrow> ('n, 't) Elem list \<Rightarrow> 'n \<Rightarrow> nat \<Rightarrow> bool"
  where "UnitInductionStep Rs x A n \<equiv> \<exists>c m. m < n \<and> ((A, c) \<in> NewUnitTransRuleSet A Rs \<or> (A, c) \<in> Rs)
              \<and> c -Rs\<rightarrow>\<^sup>m x \<and> ProducesInN [NT A] Rs (n - m) c \<and> \<not> isNTToNTProduction (A, c)"

lemma Unit_Part3:
  fixes      Rs :: "('n, 't) RuleSet"
  assumes a: "IsTerminalWord x"
  assumes b: "\<And> A. ([NT A] -Rs\<rightarrow>\<^sup>n x \<Longrightarrow> UnitInductionStep Rs x A n)"
  assumes c: "[NT A] -Rs\<rightarrow> r" 
  assumes d: "r -Rs\<rightarrow>\<^sup>n x" 
  shows      "UnitInductionStep Rs x A (n+1)"
proof-
  show ?thesis
  proof cases
    assume x: "isNTToNTProduction (A, r)"
    from x have 0: "\<exists>N'. r = [NT N']" (is "\<exists>N'. ?P N'")
      by (simp add: isNTToNTProduction_def)
    then obtain N' where 1: "?P N'" by blast
    from 1 and c have 2: "(A, N') \<in> NTToNTProductionSet Rs"
      apply(unfold ProductionStep_def Productions_def NTToNTProductionSet_def)
      by (smt (verit, ccfv_SIG) Elem.inject(1) Pair_inject append_eq_Cons_conv append_is_Nil_conv case_prodI list.discI list.inject mem_Collect_eq r_into_trancl')
    from 2 have 3: "\<And> X. (N', X) \<in> NTToNTProductionSet Rs \<Longrightarrow> (A, X) \<in> NTToNTProductionSet Rs"
      by(unfold NTToNTProductionSet_def, auto)
    from d and b and 1 have 4: "\<exists>c' m'. m' < n \<and> ((N', c') \<in> NewUnitTransRuleSet N' Rs \<or> (N', c') \<in> Rs) \<and> ProducesInN c' Rs m' x 
                         \<and> ProducesInN [NT N'] Rs (n - m') c' \<and> \<not> isNTToNTProduction (N', c')"
      (is "\<exists>c' m'. ?P c' m'")
      apply (unfold UnitInductionStep_def)
      by blast
    then obtain c' m' where 5: "?P c' m'" by blast
    from 5 have 6: "((N', c') \<in> NewUnitTransRuleSet N' Rs \<or> (N', c') \<in> Rs)"
      by auto
    then show ?thesis
    proof 
      assume x: "(N', c') \<in> NewUnitTransRuleSet N' Rs"
      from 5 and x have 7: "(A, c') \<in> NewUnitTransRuleSet A Rs"
        apply(unfold NewUnitTransRuleSet_def NTToNTProductionSet_def, simp)
        by (metis "3" NTToNTProductionSet_def isNTToNTProduction_def prod.inject)
      from 1 and 5 and c have 8: "ProducesInN [NT A] Rs (n+1 - m') c'"
        by (metis ProducesInN.simps(2) Suc_diff_le Suc_eq_plus1 order_le_less)
      from 7 have 9: " \<not> isNTToNTProduction (A, c')"
        by (metis "5" isNTToNTProduction_def snd_conv)
      from 7 and 8 and 9 and 5 show ?thesis
        apply (unfold UnitInductionStep_def)
        using trans_less_add1 by blast
    next
      assume y: "(N', c') \<in> Rs"
      from y and 5 have 7: "(A, c') \<in> NewUnitTransRuleSet A Rs"
        apply(unfold NewUnitTransRuleSet_def NTToNTProductionSet_def, simp)
        by (metis "2" NTToNTProductionSet_def isNTToNTProduction_def prod.sel(2))
      from 1 and 5 and c have 8: "ProducesInN [NT A] Rs (n+1 - m') c'"
        by (metis ProducesInN.simps(2) Suc_diff_le Suc_eq_plus1 order_le_less)
      from 7 have 9: " \<not> isNTToNTProduction (A, c')"
        by (metis "5" isNTToNTProduction_def snd_conv)
      from 7 and 8 and 9 and 5 show ?thesis
        apply (unfold UnitInductionStep_def)
        using trans_less_add1 by blast
    qed
  next
    assume y: "\<not>isNTToNTProduction (A, r)"
    have 0: "ProducesInN [NT A] Rs 1 r"
      using c by force
    from c have 1: "(A, r) \<in> Rs"
      apply(unfold ProductionStep_def Productions_def)
      by (smt (verit) CollectD Cons_eq_appendI Elem.inject(1) add_diff_cancel_right' append_Nil2 
         append_self_conv2 diff_add_0 length_0_conv length_Cons length_append list.sel(1) list.sel(3) prod.sel(1) prod.sel(2))
    from y and 0 and 1 show ?thesis 
      apply (unfold UnitInductionStep_def)
      by (metis add_diff_cancel_left' d less_add_one)
  qed
qed

lemma Unit_Part4:
  fixes      Rs :: "('n, 't) RuleSet"
  assumes a: "[NT A] -Rs\<rightarrow>\<^sup>n x"
  assumes b: "IsTerminalWord x"
  shows      "UnitInductionStep Rs x A n"
proof-
  from a and b have 0: "n > 0"
    by (metis IsTerminalWord_def ProducesInN.simps(1) bot_nat_0.not_eq_extremum list.set_intros(1))
  from 0 have 1: "\<exists>l. l = n - 1" (is "\<exists>l. ?P l")
    by auto
  then obtain l where 2: "?P l" by blast
  from b have 3: 
      "\<And> A. ([NT A] -Rs\<rightarrow>\<^sup>n x \<Longrightarrow> UnitInductionStep Rs x A n)"
    apply(induction n)
    using IsTerminalWord_def apply force
    by (metis (no_types, lifting) ProducesInN.simps(2) Suc_eq_plus1 Unit_Part3)
  from 3 and a show ?thesis by auto
qed

definition isTransformedFromRule :: "('n, 't) Elem list \<Rightarrow> ('n, 't) Elem list \<Rightarrow> ('n, 't) Rule \<Rightarrow> bool"
  where "isTransformedFromRule E1 E2 R \<equiv> \<exists> l r N rhs. (E1 = l @ (NT N) # r \<and> E2 = l @ rhs @ r \<and> R = (N, rhs))"

definition isTransformedFromNT :: "('n, 't) Elem list \<Rightarrow> ('n, 't) Elem list \<Rightarrow> 'n \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> bool"
  where "isTransformedFromNT E1 E2 N Rs \<equiv> \<exists> l r rhs. (E1 = l @ (NT N) # r \<and> E2 = l @ rhs @ r \<and> (N, rhs) \<in> Rs)"

lemma Unit_Part5:
  assumes a: "transformUnitSingle G1 N G2"
  assumes b: "\<And>m A x. (m \<le> n \<and> IsTerminalWord x \<and> A -(snd G1)\<rightarrow>\<^sup>m x \<Longrightarrow> A -(snd G2)\<rightarrow>\<^sup>* x)"
  assumes c: "ProducesInN A (snd G1) (Suc n) x"
  assumes d: "IsTerminalWord x"
  shows      "A -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from a have 0: "\<exists> S Rs1 Rs2. 
                  (S, Rs1) = G1
                  \<and> (S, Rs2) = G2
                  \<and> Rs2 = (Rs1 \<union> (NewUnitTransRuleSet N Rs1)) - (NTToNTSetForA N)"
          (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformUnitSingle_def)
  then obtain S Rs1 Rs2 where r: "?P S Rs1 Rs2" by blast
  from r have e: "G1 = (S, Rs1)" by auto
  from r have f: "G2 = (S, Rs2)" by auto
  from r have g: "Rs2 = (Rs1 \<union> (NewUnitTransRuleSet N Rs1)) - (NTToNTSetForA N)" by auto
  from c and e have 1: "\<exists> t. ProducesInN t Rs1 n x \<and> A -Rs1\<rightarrow> t"
    (is "\<exists> t. ?P t")
    by auto
  then obtain t where 2: "?P t" by blast
  have 3: "isTransformedFromNT A t N Rs1 \<or> \<not>isTransformedFromNT A t N Rs1" by auto
  
  then show ?thesis

  proof
    assume x: "isTransformedFromNT A t N Rs1"
    from x have 4: "\<exists> l r rhs. (A = l @ (NT N) # r \<and> t = l @ rhs @ r \<and> (N, rhs) \<in> Rs1)" (is "\<exists> l r rhs. ?P l r rhs")
      by (simp add: isTransformedFromNT_def)
    then obtain l r rhs where 5: "?P l r rhs" by blast
    from c and 5 have 6: "\<exists> l1 nr n1. n1 \<le> n+1 \<and> x = l1 @ nr \<and> ProducesInN l Rs1 n1 l1 \<and> ProducesInN ([NT N] @ r) Rs1 (n+1-n1) nr"
      (is "\<exists> l1 nr n1. ?P l1 nr n1")
      by (simp, metis c e productionParts6 sndI)
    then obtain l1 nr n1 where 7: "?P l1 nr n1" by blast
    from 7 have 8: "\<exists> x1 r1 n2. n2 \<le> (n+1-n1) \<and> nr = x1 @ r1 \<and> ProducesInN r Rs1 (n+1-n1-n2) r1 \<and> ProducesInN ([NT N]) Rs1 (n2) x1"
      (is "\<exists> x1 r1 n2. ?P x1 r1 n2")
      by (metis productionParts6)
    then obtain x1 r1 n2 where 9: "?P x1 r1 n2" by blast
    from 9 and b a and d have 10: "UnitInductionStep Rs1 x1 N n2"
      by (simp add: "7" IsTerminalWord_def Unit_Part4)
    from 10 have 11: "\<exists>c m. m < n2 \<and> ((N, c) \<in> NewUnitTransRuleSet N Rs1 \<or> (N, c) \<in> Rs1) \<and> c -Rs1\<rightarrow>\<^sup>m x1 \<and> [NT N] -Rs1\<rightarrow>\<^sup>(n2 - m) c \<and> \<not> isNTToNTProduction (N, c)"
      (is "\<exists> c m. ?P c m")
      by (simp add: UnitInductionStep_def)
    then obtain cx mx where 12: "?P cx mx" by blast
    from 9 and 7 have 13: "x = l1 @ x1 @ r1" by auto
    from d and 13 have 14: "IsTerminalWord l1"
      by (simp add: IsTerminalWord_def)
    from d and 13 have 15: "IsTerminalWord x1"
      by (simp add: IsTerminalWord_def)
    from d and 13 have 16: "IsTerminalWord r1"
      by (simp add: IsTerminalWord_def)
    from 9 and 7 have 17: "mx \<le> n"
      by (metis "12" Suc_eq_plus1 diff_le_self less_Suc_eq_le order_less_le_trans)
    from 15 and 12 have 18: "n2 \<ge> 1"
      by simp
    from 18 and 9 and 7 have 19: "n1 \<le> n"
      by linarith
    from 18 have 20: "n+1-n1-n2 \<le> n" 
      by linarith
    from 19 and b  and 7 have 21: "l -Rs2\<rightarrow>\<^sup>* l1"
      using "14" e f by auto
    from 20 and b and 9 have 22: "r -Rs2\<rightarrow>\<^sup>* r1"
      using "16" e f by auto
    from 12 have 23: "mx \<le> n"
      using "17" by linarith
    from b and 12 and 23 have 24: "cx -Rs2\<rightarrow>\<^sup>* x1"
      using "15" e f by auto
    from 12 have 25: "(N, cx) \<notin> (NTToNTSetForA N)"
      by (smt (verit, del_insts) CollectD NTToNTSetForA_def isNTToNTProduction_def)
    from 25 and 12 have 26: "(N, cx) \<in> Rs2"
      using r by fastforce
    from 26 have 27: "[NT N] -Rs2\<rightarrow> cx"
      using ProductionStep_def Productions_def by fastforce
    from 27 and 24 have 28: "[NT N] -Rs2\<rightarrow>\<^sup>* x1"
      by (meson ProducesInN.simps(2) Produces_def)
    from 28 and 21 have 29: "l @ [NT N] -Rs2\<rightarrow>\<^sup>* l1 @ x1"
      by (simp add: productionParts4)
    from 29 and 22 have 30: "l @ [NT N] @ r -Rs2\<rightarrow>\<^sup>* l1 @ x1 @ r1"
      by (meson "21" "28" productionParts4)
    from 30 show ?thesis
      by (simp add: "13" "5" f)
  next
    assume y: "\<not> isTransformedFromNT A t N Rs1"
    from 2 have 4: "\<exists> l r rhs N'. (A = l @ (NT N') # r \<and> t = l @ rhs @ r \<and> (N', rhs) \<in> Rs1 \<and> ProducesInN t Rs1 n x)" (is "\<exists> l r rhs N'. ?P l r rhs N'")
      by(unfold ProductionStep_def Productions_def, auto)
    then obtain l r rhs N' where 5: "?P l r rhs N'" by blast
    from 5 and y have 6: "N' \<noteq> N" 
      by(simp add: isTransformedFromNT_def, auto)
    from 6 have 7: "(N', rhs) \<notin> (NTToNTSetForA N)"
      by (simp add: NTToNTSetForA_def)
    from 7 and 5 and g have 8: "(N', rhs) \<in> Rs2"
      by auto
    from 8 have 9: "[NT N'] -Rs2\<rightarrow> rhs" 
      by (simp add: ProductionStep_def Productions_def, force)
    from 4 have 10: "ProducesInN t Rs1 n x" by auto
    from 10 and b have 11: "t -Rs2\<rightarrow>\<^sup>* x"
      using d e f by auto
    from 9 and 5 have 12: "A -Rs2\<rightarrow> t"
      using productionAppend1 by fastforce
    from 12 and 11 and f show ?thesis
      by (auto, meson ProducesInN.simps(2) Produces_def)
  qed
qed

lemma Unit_Part6:
  assumes a: "transformUnitSingle G1 N G2"
  assumes b: "\<And>m A x. (m < n \<and> IsTerminalWord x \<and> A -(snd G1)\<rightarrow>\<^sup>m x \<Longrightarrow> A -(snd G2)\<rightarrow>\<^sup>* x)"
  assumes c: "ProducesInN A (snd G1) n x"
  assumes d: "IsTerminalWord x"
  shows      "A -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  show ?thesis
  proof cases
    assume x: "n = 0"
    from x and c have 0: "A = x"
      by simp
    from 0 show ?thesis
      by (meson ProducesInN.simps(1) Produces_def)
  next
    assume y: "n \<noteq> 0"
    from y have 0: "\<exists> l. l = n-1" (is "\<exists> l. ?P l")
      by blast
    then obtain l where 1: "?P l" by blast
    from 1 and b have 2: "\<And>m A x. (m \<le> l \<and> IsTerminalWord x \<and> A -(snd G1)\<rightarrow>\<^sup>m x \<Longrightarrow> A -(snd G2)\<rightarrow>\<^sup>* x)"
      by (metis Suc_pred' bot_nat_0.not_eq_extremum le_imp_less_Suc y)
    from c and 1 have 3: "ProducesInN A (snd G1) (l+1) x"
      using y by fastforce
    from 2 and 3 and d and a show ?thesis
      by (metis One_nat_def Unit_Part5 add.right_neutral add_Suc_right)
  qed
qed

lemma Unit_Part7:
  assumes a: "transformUnitSingle G1 N G2"
  assumes b: "ProducesInN A (snd G1) n x"
  assumes c: "IsTerminalWord x"
  shows      "A -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  have 0: "\<And>m A x. (m < n \<and> IsTerminalWord x \<and> A -(snd G1)\<rightarrow>\<^sup>m x \<Longrightarrow> A -(snd G2)\<rightarrow>\<^sup>* x)"
    apply(induction n rule: less_induct)
    by (meson Unit_Part6 a)
  from 0 and c and b show ?thesis
    by (metis Unit_Part6 a)
qed

lemma Unit_Part8:
  assumes a: "transformUnitSingle G1 N G2"
  assumes b: "x \<in> \<lbrakk>G1\<rbrakk>"
  shows      "x \<in> \<lbrakk>G2\<rbrakk>"
proof-
  from b have 0: "\<exists>n. ProducesInN [NT (fst G1)] (snd G1) n x"
    by (unfold Lang_def Language_def PartialEvalLanguage_def Produces_def, auto)
  from b have 1: "IsTerminalWord x"
    by (unfold Lang_def Language_def PartialEvalLanguage_def Produces_def, auto)
  from a and 0 and 1 have 2: "[NT (fst G1)] -(snd G2)\<rightarrow>\<^sup>* x"
    by (meson Unit_Part7)
  from 2 and 1 and a show ?thesis
    by(simp add: transformUnitSingle_def Lang_def Language_def PartialEvalLanguage_def, force)
qed

lemma Unit_Part9:
  assumes a: "transformUnitSingle G1 N G2"
  assumes b: "\<And>A x. (IsTerminalWord x \<and> ProducesInN A (snd G2) n x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
  assumes c: "ProducesInN A (snd G2) (Suc n) x"
  assumes d: "IsTerminalWord x"
  shows      "A -(snd G1)\<rightarrow>\<^sup>* x"
proof-
  from a have 0: "\<exists> S Rs1 Rs2. 
                  (S, Rs1) = G1
                  \<and> (S, Rs2) = G2
                  \<and> Rs2 = (Rs1 \<union> (NewUnitTransRuleSet N Rs1)) - (NTToNTSetForA N)"
          (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformUnitSingle_def)
  then obtain S Rs1 Rs2 where r: "?P S Rs1 Rs2" by blast
  from r have e: "G1 = (S, Rs1)" by auto
  from r have f: "G2 = (S, Rs2)" by auto
  from r have g: "Rs2 = (Rs1 \<union> (NewUnitTransRuleSet N Rs1)) - (NTToNTSetForA N)" by auto
  from c and f have 1: "\<exists> t. ProducesInN t Rs2 n x \<and> A -Rs2\<rightarrow> t"
    (is "\<exists> t. ?P t")
    by auto
  then obtain t where 2: "?P t" by blast
  from 2 and b and d and e and f have 3: "t -(snd G1)\<rightarrow>\<^sup>* x" 
    by force
  from 1 have 4: "\<exists> l r rhs N'. (N', rhs) \<in> Rs2 \<and> A = l @ [NT N'] @ r \<and> t = l @ rhs @ r" 
      (is "\<exists> l r rhs N'. ?P l r rhs N'")
    by (smt (verit, del_insts) "2" Pair_inject ProductionStep_def Productions_def append_Cons append_Nil mem_Collect_eq)
  then obtain l r rhs N' where 5: "?P l r rhs N'" by blast
  from 5 and g have 6: "(N', rhs) \<in> Rs1 \<or> (N', rhs) \<in> NewUnitTransRuleSet N Rs1"
    by fastforce
  then show ?thesis
  proof
    assume x: "(N', rhs) \<in> Rs1"
    from x and 5 have 7: "A -Rs1\<rightarrow> t"
      using CollectI ProductionStep_def Productions_def by fastforce
    from 3 and 7 and e show ?thesis
      by (metis ProducesInN.simps(2) Produces_def snd_conv)
  next
    assume y: "(N', rhs) \<in> NewUnitTransRuleSet N Rs1"
    from y have 7: "N' = N"
      by(simp add: NewUnitTransRuleSet_def, auto)
    from y and 7 have 8: "[NT N] -Rs1\<rightarrow>\<^sup>* rhs"
      by (simp add: Unit_Part2)
    from 8 have 9: "l @ [NT N] @ r -Rs1\<rightarrow>\<^sup>* l @ rhs @ r"
      using productionAppend3 by blast
    from 9 and 5 have 10: "A -Rs1\<rightarrow>\<^sup>* t"
      using "7" by blast
    from 10 and 3 show ?thesis
      using e transitiveProductions by auto
  qed
qed

lemma Unit_Part10:
  assumes a: "transformUnitSingle G1 N G2"
  assumes b: "ProducesInN A (snd G2) n x"
  assumes c: "IsTerminalWord x"
  shows      "A -(snd G1)\<rightarrow>\<^sup>* x"
proof-
  have 0: "\<And>A x. (IsTerminalWord x \<and> A -(snd G2)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
    apply(induction n)
    apply (metis ProducesInN.simps(1) Produces_def)
    by (meson Unit_Part9 a)
  from 0 show ?thesis
    using b c by blast
qed

lemma Unit_Part11:
  assumes a: "transformUnitSingle G1 N G2"
  assumes b: "x \<in> \<lbrakk>G2\<rbrakk>"
  shows      "x \<in> \<lbrakk>G1\<rbrakk>"
proof-
  from b have 0: "\<exists>n. ProducesInN [NT (fst G2)] (snd G2) n x"
    by (unfold Lang_def Language_def PartialEvalLanguage_def Produces_def, auto)
  from b have 1: "IsTerminalWord x"
    by (unfold Lang_def Language_def PartialEvalLanguage_def Produces_def, auto)
  from a and 0 and 1 have 2: "[NT (fst G2)] -(snd G1)\<rightarrow>\<^sup>* x"
    by (meson Unit_Part10)
  from 2 and 1 and a show ?thesis
    by(simp add: transformUnitSingle_def Lang_def Language_def PartialEvalLanguage_def, force)
qed

lemma verifyUnitTransform:
  assumes a: "transformUnitSingle G1 N G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (simp add: Unit_Part8)
  from a have 1: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (simp add: Unit_Part11)
  from 0 and 1 show ?thesis
    by fastforce
qed

definition DelSingleNTFromElemListSet :: "'n \<Rightarrow> (('n, 't) Elem list \<times> ('n, 't) Elem list) set"
  where "DelSingleNTFromElemListSet N \<equiv> {((l @ r), (l @ NT(N) # r)) | l r. True}"

definition DelNTFromElemListSet :: "'n \<Rightarrow> (('n, 't) Elem list \<times> ('n, 't) Elem list) set"
  where "DelNTFromElemListSet N \<equiv> {((l @ r), (l @ NT(N) # r)) | l r. True}\<^sup>*"

definition DelNTFromRuleSet :: "'n \<Rightarrow> (('n, 't) Rule \<times> ('n, 't) Rule) set"
  where "DelNTFromRuleSet N \<equiv> {((S, l @ r), (S, l @ NT(N) # r)) | S l r. True}\<^sup>*"

definition DelNTFromRule :: "'n \<Rightarrow> ('n, 't) Rule set \<Rightarrow> ('n, 't) Rule set"
  where "DelNTFromRule N R \<equiv> { NR | NR OR. (NR, OR) \<in> DelNTFromRuleSet N \<and> OR \<in> R }"

definition DelAllNullableNTsFromRules :: "('n, 't) RuleSet \<Rightarrow> ('n, 't) RuleSet"
  where "DelAllNullableNTsFromRules X = {R | R N. R \<in> DelNTFromRule N X \<and> Nil \<in> \<lbrakk>N\<rbrakk>\<^sub>X}"

definition DelAllNullableNTsFromElemList :: "('n, 't) Elem list \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> ('n, 't) Elem list set"
  where "DelAllNullableNTsFromElemList E1 X = {E | E N. (E, E1) \<in> DelNTFromElemListSet N \<and> Nil \<in> \<lbrakk>N\<rbrakk>\<^sub>X}"

definition RemoveAllEpsilonProds :: "'n \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> ('n, 't) RuleSet"
  where "RemoveAllEpsilonProds S X = {R | R N Rhs. R \<in> X \<and> (N, Rhs) = R \<and> (N = S \<or> Rhs \<noteq> Nil)}"

definition transformDel :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformDel G1 G2 \<equiv> \<exists> S Rs1 Rs2.
                               (S, Rs1) = G1
                               \<and> (S, Rs2) = G2
                               \<and> Rs2 = RemoveAllEpsilonProds S (Rs1 \<union> DelAllNullableNTsFromRules Rs1)"

definition delStep :: "'n \<Rightarrow> ('n, 't) Elem list \<Rightarrow> ('n, 't) Elem list \<Rightarrow> bool"
  where "delStep N E1 E2 \<equiv> (E2, E1) \<in> DelSingleNTFromElemListSet N"

fun delInN :: "'n \<Rightarrow> nat \<Rightarrow> ('n, 't) Elem list \<Rightarrow> ('n, 't) Elem list \<Rightarrow> bool"
  where "delInN N 0 E1 E2 = (E1 = E2)" |
        "delInN N (Suc a) E1 E2 = (\<exists>t. (delStep N E1 t) \<and> (delInN N a t E2))"

definition delNT :: "'n \<Rightarrow> ('n, 't) Elem list \<Rightarrow> ('n, 't) Elem list \<Rightarrow> bool"
  where "delNT N E1 E2 \<equiv> \<exists> n. delInN N n E1 E2"

lemma Del_Part1:
  assumes a: "delInN N n1 A B"
  assumes b: "delInN N n2 B C"
  shows      "delInN N (n1 + n2) A C"
proof-
  have 0: "\<And> A B C m. delInN N n1 A B \<and> delInN N m B C \<Longrightarrow> delInN N (n1+m) A C"
    apply(induction n1)
    apply simp
    by auto
  from a and b and 0 show ?thesis
    by force
qed

lemma Del_Part2:
  assumes a: "delNT N A B"
  assumes b: "delNT N B C"
  shows      "delNT N A C"
proof-
  from a and b and Del_Part1 show ?thesis
    apply(unfold delNT_def)
    by fastforce
qed

lemma Del_Part3:
  assumes a: "(delNT N)\<^sup>+\<^sup>+ a b"
  shows      "(delNT N) a b"
proof-
  from Del_Part2 and a show ?thesis
    by (smt (verit, ccfv_SIG) tranclp_induct)
qed

lemma Del_Part4:
  shows      "(delNT N)\<^sup>+\<^sup>+ = delNT N"
proof-
  from Del_Part3 show ?thesis
    by fastforce
qed

lemma Del_Part5:
  assumes a: "(delStep N) a b"
  shows      "(delNT N) a b"
proof-
  from a show ?thesis
    by (meson delInN.simps(1) delInN.simps(2) delNT_def)
qed

lemma Del_Part6:
  shows      "(delNT N)\<^sup>*\<^sup>* = delNT N"
proof-
  have 0: "\<And> a. (delNT N) a a"
    by (meson delInN.simps(1) delNT_def)
  from Del_Part4 and 0 show ?thesis
    by (metis antisym_conv predicate2I r_into_rtranclp rtranclp_into_tranclp1)
qed

lemma Del_Part7:
  assumes a: "(delStep N)\<^sup>*\<^sup>* a b"
  shows      "(delNT N) a b"
proof-
  from a have 0: "(delNT N)\<^sup>*\<^sup>* a b"
    by (metis Del_Part5 mono_rtranclp)
  from 0 and Del_Part6 show ?thesis
    by metis
qed

lemma Del_Part8:
  assumes a: "(delNT N) a b" 
  shows      "(delStep N)\<^sup>*\<^sup>* a b"
proof-
  from a have 0: "\<exists> n. delInN N n a b" (is "\<exists> n. ?P n")
    by(unfold delNT_def, auto)
  then obtain n where 1: "?P n" by blast
  have 2: "\<And>a b. delInN N n a b \<Longrightarrow> (delStep N)\<^sup>*\<^sup>* a b"
    apply(induction n)
    apply simp
    by (meson delInN.simps(2) rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl rtranclp_trans)
  from 1 and 2 show ?thesis
    by blast
qed

lemma Del_Part9:
  shows      "(delNT N) = (delStep N)\<^sup>*\<^sup>*"
proof-
  show ?thesis
    using Del_Part7 Del_Part8 by fastforce
qed

lemma Del_Part10:
  fixes      S :: "('a \<times> 'a) set"
  fixes      R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes a: "\<And> a b. R a b \<longleftrightarrow> (b, a) \<in> S"
  shows      "R\<^sup>*\<^sup>* a b \<longleftrightarrow> (b, a) \<in> S\<^sup>*"
proof-
  from a show ?thesis
    by (smt (verit) Transitive_Closure.rtranclp_rtrancl_eq converse_rtranclp_induct 
        rtrancl.rtrancl_into_rtrancl rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
qed

lemma Del_Part11:
  shows      "(delNT N) a b \<longleftrightarrow> (b, a) \<in> DelNTFromElemListSet N"
proof-
  have 0: "\<And> a b. delStep N a b \<longleftrightarrow> (b, a) \<in> DelSingleNTFromElemListSet N"
    apply(unfold delStep_def DelSingleNTFromElemListSet_def)
    by force
  have 1: "DelNTFromElemListSet N = (DelSingleNTFromElemListSet N)\<^sup>*"
    by(unfold DelNTFromElemListSet_def DelSingleNTFromElemListSet_def, auto)
  from Del_Part9 and Del_Part10 and 0 and 1 show ?thesis
    by metis
qed

lemma Del_Part12:
  assumes a: "(delStep N) (l @ r) X"
  shows      "(\<exists> l'. (delStep N) l l' \<and> X = l' @ r) \<or> (\<exists> r'. (delStep N) r r' \<and> X = l @ r')"   
proof-
  from a have 0: "\<exists>a b. l @ r = (a @ [NT N] @ b) \<and> X = (a @ b)" (is "\<exists> a b. ?P a b")
    by(unfold delStep_def DelSingleNTFromElemListSet_def, auto) 
  then obtain a b where 1: "?P a b" by blast
  from 1 have 3: "(size l \<ge> size (a @ [NT N])) \<Longrightarrow> \<exists> c. l = (a @ [NT N]) @ c"
    by (metis append.assoc listPrefixSize)
  have 4: "size l > size a \<Longrightarrow> size l \<ge> size (a @ [NT N])"
    by simp
  from 1 have 5: "size l + size r = size a + size ([NT N] @ b)"
    by (metis length_append)
  from 5 have 6: "size l \<le> size a \<Longrightarrow> size r \<ge> size ([NT N] @ b)"
    by linarith
  from 1 have 7: "size r \<ge> size ([NT N] @ b) \<Longrightarrow> \<exists> c. r = c @ ([NT N] @ b)"
    by (metis listSuffixSize)
  have 2: "((size l) > (size a)) \<or> ((size l) \<le> size a)"
    using linorder_not_less by blast
  then show ?thesis
  proof
    assume x: "(size l) > (size a)"
    from x and 4 have 8: "size l \<ge> size (a @ [NT N])"
      by auto
    from 8 and 3 have 9:"\<exists> c. l = (a @ [NT N]) @ c" (is "\<exists> c. ?P c")
      by auto
    then obtain c where 10: "?P c" by blast
    from 10 and 1 have 11: "(delStep N) l (a @ c)"
      apply(unfold delStep_def, auto) 
      using delStep_def DelSingleNTFromElemListSet_def by fastforce
    from 10 and 1 have 12: "c @ r = b" by simp
    from 1 and 12 and 11 have 13: "\<exists> l'. (delStep N) l l' \<and> X = l' @ r"
      by force
    show ?thesis
      by (simp add: "13")
  next
    assume y: "((size l) \<le> size a)"
    from y and 6 have 8: "size r \<ge> size ([NT N] @ b)"
      by auto
    from 8 and 7 have 9: "\<exists> c. r = c @ ([NT N] @ b)" (is "\<exists> c. ?P c")
      by auto
    then obtain c where 10: "?P c" by blast
    from 10 and 1 have 11: "(delStep N) r (c @ b)"
      apply(unfold delStep_def, auto) 
      using delStep_def DelSingleNTFromElemListSet_def by fastforce
    from 10 and 1 have 12: "l @ c = a" by simp
    from 1 and 12 and 11 have 13: "\<exists> r'. (delStep N) r r' \<and> X = l @ r'"
      by force
    show ?thesis
      by (simp add: "13")
  qed
qed  

lemma Del_Part13:    
  assumes a: "\<And>l r. (delInN N n (l @ r) X) \<Longrightarrow> (\<exists>l' r'. delNT N l l' \<and> delNT N r r' \<and> l' @ r' = X)"
  assumes b: "delInN N (n+1) (l@r) X"
  shows      "\<exists>l' r'. delNT N l l' \<and> delNT N r r' \<and> l' @ r' = X"
proof-
  from b have 0: "\<exists> q. delStep N (l@r) q \<and> delInN N n q X" (is "\<exists> q. ?P q")
    by auto  
  then obtain q where 1 : "?P q" by blast
  from 1 and Del_Part12 have 2:"(\<exists> l'. delStep N l l' \<and> l' @ r = q) \<or> (\<exists> r'. delStep N r r' \<and> l @ r' = q)"
    by metis
  have 3: "\<And> x. delInN N 0 x x" 
    by simp
  from 3 have 4: "\<And> x. delNT N x x" 
    using delNT_def by metis
  from 1 have 5: "\<exists>l1 r1. delNT N l l1 \<and> delNT N r r1 \<and> l1 @ r1 = q" (is "\<exists> l1 r1. ?P l1 r1")
    by (meson "2" "4" Del_Part5)
  then obtain l1 r1 where 6: "?P l1 r1" by blast
  from 1 and 6 have 7: "delInN N n (l1@r1) X"
    by blast
  from a and 7 have 8: "\<exists>l' r'. delNT N l1 l' \<and> delNT N r1 r' \<and> l' @ r' = X" (is "\<exists> l' r'. ?P l' r'")
    by blast
  then obtain l' r' where 9: "?P l' r'" by blast
  from 9 and 6 and 2 show ?thesis
    by (metis Del_Part2)
qed

lemma Del_Part14:
  assumes a: "delNT N (l @ r) X"
  shows      "\<exists> l' r'. delNT N l l' \<and> delNT N r r' \<and> l' @ r' = X"
proof-
  from a have 0: "\<exists> n. delInN N n (l @ r) X" (is "\<exists> n. ?P n")
    by (simp add: delNT_def)
  then obtain n where 1: "?P n" by blast
  have 2: "\<And> l r. (delInN N n (l @ r) X) \<Longrightarrow> (\<exists>l' r'. delNT N l l' \<and> delNT N r r' \<and> l' @ r' = X)"
    apply(induction n)
     apply (meson delInN.simps(1) delNT_def)
    by (smt (verit, ccfv_threshold) Del_Part13 One_nat_def add.right_neutral add_Suc_right)
  from 2 and 1 show ?thesis
    by force
qed

lemma Del_Part15:
  assumes a: "(A', l@r) \<in> DelNTFromElemListSet N"
  shows      "\<exists> l' r'. (l', l) \<in> DelNTFromElemListSet N \<and> (r', r) \<in> DelNTFromElemListSet N \<and> A' = l' @ r'"
proof-
  from a show ?thesis
    by (metis Del_Part11 Del_Part14)
qed

lemma Del_Part16:
  assumes a: "A' \<in>  DelAllNullableNTsFromElemList (l@r) Rs"
  shows      "\<exists> l' r'. l' \<in> DelAllNullableNTsFromElemList l Rs \<and> r' \<in> DelAllNullableNTsFromElemList r Rs \<and> A' = l' @ r'"
proof-
  from a show ?thesis
    apply(unfold DelAllNullableNTsFromElemList_def) 
    using Del_Part15 by fastforce
qed

lemma Del_Part17:
  assumes a: "(R1, R2) \<in> DelNTFromRuleSet N"
  shows      "fst R1 = fst R2"
proof-
  from a show ?thesis
    apply(simp add: DelNTFromRuleSet_def)
    by(induction rule: rtrancl.induct, auto)
qed

lemma Del_Part18:
  assumes a: "(R, R') \<in> DelNTFromRuleSet N"
  assumes b: "R = (S, rhs)"
  shows      "\<exists> rhs'. (rhs, rhs') \<in> DelNTFromElemListSet N \<and> R' = (S, rhs')"
proof-
  from a and b show ?thesis
    apply(simp add: DelNTFromRuleSet_def)
    apply(induction rule: rtrancl.induct)
     apply(simp add: DelNTFromElemListSet_def)
    using b apply blast
    by (smt (verit, ccfv_threshold) DelNTFromElemListSet_def Pair_inject mem_Collect_eq rtrancl.simps)
qed    

lemma Del_Part19:
  assumes a: "(rhs, rhs') \<in> DelNTFromElemListSet N"
  shows      "((S, rhs), (S, rhs')) \<in> DelNTFromRuleSet N"
proof-
  from a show ?thesis
    apply(simp add: DelNTFromElemListSet_def)
    apply(induction rule: rtrancl.induct)
    apply(simp add: DelNTFromRuleSet_def)
    apply(simp add: DelNTFromRuleSet_def)
    by (simp add: rtrancl.rtrancl_into_rtrancl)
qed
    
lemma Del_Part20:
  assumes a: "Rs2 = (Rs1 \<union> DelAllNullableNTsFromRules Rs1)"
  assumes b: "[NT A] -Rs1\<rightarrow> rhs"
  assumes c: "rhs' \<in> DelAllNullableNTsFromElemList rhs Rs1"
  shows      "(A, rhs') \<in> Rs2"
proof-
  from b have 0: "(A, rhs) \<in> Rs1"
    by (smt (verit, ccfv_SIG) Elem.inject(1) Pair_inject ProductionStep_def Productions_def 
        append.right_neutral append_Nil append_eq_Cons_conv append_is_Nil_conv list.discI list.inject mem_Collect_eq)
  from a and 0 and c have 1: "(A, rhs') \<in> Rs2"
    apply(simp add: DelAllNullableNTsFromRules_def DelAllNullableNTsFromElemList_def DelNTFromRule_def)
    by (meson Del_Part19)
  from 1 show ?thesis
    by auto
qed

lemma Del_Part21:
  assumes a: "transformDel G1 G2"
  assumes b: "[NT A] -(snd G1)\<rightarrow> rhs"
  assumes c: "rhs' \<noteq> Nil"
  assumes d: "rhs' \<in> DelAllNullableNTsFromElemList rhs (snd G1)"
  shows      "(A, rhs') \<in> (snd G2)"
proof-
  from a have 0: "\<exists> S Rs1 Rs2. 
                  (S, Rs1) = G1
                  \<and> (S, Rs2) = G2
                  \<and> Rs2 = RemoveAllEpsilonProds S (Rs1 \<union> DelAllNullableNTsFromRules Rs1)"
          (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformDel_def)
  then obtain S Rs1 Rs2 where 1: "?P S Rs1 Rs2" by blast
  from c have 2: "\<And> H. (A, rhs') \<in> H \<Longrightarrow> (A, rhs') \<in> RemoveAllEpsilonProds S H"
    apply(unfold RemoveAllEpsilonProds_def) 
    by blast
  have 3: "(A, rhs') \<in> (Rs1 \<union> DelAllNullableNTsFromRules Rs1)" 
    by (metis "1" Del_Part20 b d snd_conv)
  from 3 and 2 have 4: "(A, rhs') \<in> Rs2"
    using "1" by presburger
  from 4 and 1 show ?thesis
    by force
qed

lemma Del_Part22:
  assumes a: "delStep N a a'"
  shows      "delStep N (l@a@r) (l@a'@r)"
proof-
  from a show ?thesis
    apply(unfold delStep_def DelSingleNTFromElemListSet_def)
    by (smt (verit, best) append.assoc append_Cons mem_Collect_eq prod.inject)
qed

lemma Del_Part23:
  assumes a: "delInN N n a a'"
  shows      "delInN N n (l@a@r) (l@a'@r)"
proof-
  have 0: "\<And> N a a'. delInN N n a a' \<Longrightarrow> delInN N n (l@a@r) (l@a'@r)"
    apply(induction n)
     apply auto[1]
    by (meson Del_Part22 delInN.simps(2))
  from 0 show ?thesis
    using assms by blast
qed

lemma Del_Part24:
  assumes a: "delNT N a a'"
  shows      "delNT N (l@a@r) (l@a'@r)"
proof-
  from a have 0: "\<exists> n. delInN N n a a'" (is "\<exists>n. ?P n")
    by (simp add: delNT_def)
  then obtain n where 1: "?P n" by blast
  from 1 have 2: "delInN N n (l@a@r) (l@a'@r)"
    by (simp add: Del_Part23)
  from 2 show ?thesis
    by (simp add: delNT_def, auto)
qed

lemma Del_Part25:
  assumes a: "delNT N l l'"
  assumes b: "delNT N r r'"
  shows      "delNT N (l@r) (l'@r')"
proof-
  from a have 0: "delNT N (l@r) (l'@r)"
    by (metis Del_Part24 append_self_conv2)
  from 0 and b have 1: "delNT N (l'@r) (l'@r')"
    by (metis Del_Part24 append.right_neutral)
  from 0 and 1 show ?thesis
    by (meson Del_Part2)
qed

lemma Del_Part26:
  assumes a: "(a, a') \<in> DelNTFromElemListSet N"
  shows      "((l@a@r), (l@a'@r)) \<in> DelNTFromElemListSet N "
proof-
  from a and Del_Part24 show ?thesis
    by (metis Del_Part11)
qed

lemma Del_Part27:
  assumes a: "a' \<in> DelAllNullableNTsFromElemList a Rs1"
  shows      "(l@a'@r) \<in> DelAllNullableNTsFromElemList (l@a@r) Rs1 "
proof-
  from a show ?thesis
    apply(unfold DelAllNullableNTsFromElemList_def)
    using Del_Part26 by fastforce
qed

lemma Del_Part28:
  assumes a: "(l', l) \<in> DelNTFromElemListSet N"
  assumes b: "(r', r) \<in> DelNTFromElemListSet N"
  shows      "((l'@r'), (l@r)) \<in> DelNTFromElemListSet N"
proof-
  from a and b and Del_Part25 show ?thesis
    by (metis Del_Part11)
qed

lemma Del_Part29:
  assumes a: "l' \<in> DelAllNullableNTsFromElemList l Rs1"
  assumes b: "r' \<in> DelAllNullableNTsFromElemList r Rs1"
  shows      "(l'@r') \<in> DelAllNullableNTsFromElemList (l@r) Rs1"
proof-
  from a have 0: "(l'@r) \<in> DelAllNullableNTsFromElemList (l@r) Rs1"
    apply(simp add: DelAllNullableNTsFromElemList_def)
    by (metis Del_Part26 append.left_neutral)
  from b and 0 have 1: "(l'@r') \<in> DelAllNullableNTsFromElemList (l'@r) Rs1"
    apply(simp add: DelAllNullableNTsFromElemList_def)
    by (metis Del_Part26 append.right_neutral)
  from 0 and 1 show ?thesis
    apply(simp add: DelAllNullableNTsFromElemList_def)
    sledgehammer
qed

lemma Del_Part27:
  assumes a: "transformDel G1 G2"
  assumes b: "\<And>m A x. (m \<le> n \<and> x \<noteq> Nil \<and> A -(snd G1)\<rightarrow>\<^sup>m x \<Longrightarrow> \<exists> A'. A' \<in> DelAllNullableNTsFromElemList A (snd G1) \<and> A' -(snd G2)\<rightarrow>\<^sup>* x)"
  assumes c: "ProducesInN A (snd G1) (n+1) x"
  assumes e: "x \<noteq> Nil"
  shows      "\<exists> A'. A' \<in> DelAllNullableNTsFromElemList A (snd G1) \<and> A' -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from a have 0: "\<exists> S Rs1 Rs2. 
                  (S, Rs1) = G1
                  \<and> (S, Rs2) = G2
                  \<and> Rs2 = RemoveAllEpsilonProds S (Rs1 \<union> DelAllNullableNTsFromRules Rs1)"
          (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformDel_def)
  then obtain S Rs1 Rs2 where r: "?P S Rs1 Rs2" by blast
  from r have f: "G1 = (S, Rs1)" by auto
  from r have g: "G2 = (S, Rs2)" by auto
  from r have h: "Rs2 = RemoveAllEpsilonProds S (Rs1 \<union> DelAllNullableNTsFromRules Rs1)" by auto
  from c and f have 1: "\<exists> t. ProducesInN t Rs1 n x \<and> A -Rs1\<rightarrow> t"
    (is "\<exists> t. ?P t")
    by auto
  then obtain t where 2: "?P t" by blast
  from 2 have 3: "\<exists> l r N rhs. A = l @ [NT N] @ r \<and> t = l @ rhs @ r \<and> (N, rhs) \<in> Rs1"
    (is "\<exists> l r N rhs. ?P l r N rhs")
    by(unfold ProductionStep_def Productions_def, auto)
  then obtain l r N rhs where 4: "?P l r N rhs" by blast
  from 2 and b and e and g and f have 5: "\<exists> t'. t' \<in> DelAllNullableNTsFromElemList t Rs1 \<and> t' -Rs2\<rightarrow>\<^sup>* x"
    (is "\<exists> t'. ?P t'")
    by auto
  then obtain t' where 6: "?P t'" by blast
  from 6 have 7: "\<exists> l' rr'. t' = l' @ rr' \<and> l' \<in> DelAllNullableNTsFromElemList l Rs1 \<and> rr' \<in> DelAllNullableNTsFromElemList (rhs@r) Rs1"
    (is "\<exists> l' rr'. ?P l' rr'")
    using "4" Del_Part16 by fastforce
  then obtain l' rr' where 8: "?P l' rr'" by blast
  from 8 have 9: "\<exists> r' rhs'. rr' = rhs' @ r' \<and> r' \<in> DelAllNullableNTsFromElemList r Rs1 \<and> rhs' \<in> DelAllNullableNTsFromElemList rhs Rs1"
    (is "\<exists> r' rhs'. ?P r' rhs'")
    using Del_Part16 by fastforce
  then obtain r' rhs' where 10: "?P r' rhs'" by blast
  show ?thesis
  proof cases
    assume x: "rhs = Nil"
    from x and 4 have 11: "(N, []) \<in> Rs1" by auto
    from 10 have 12: "rhs' \<in> DelAllNullableNTsFromElemList rhs Rs1" by auto
    from 12 and x have 13: "rhs' = Nil"
      apply(unfold DelAllNullableNTsFromElemList_def DelNTFromElemListSet_def)
      by (smt (verit, del_insts) CollectD append_is_Nil_conv list.discI rtrancl.simps snd_conv)
    from 13 have 14: "t' = l' @ r'"
      by (simp add: "10" "8")
    from 11 have 15: "[NT N] -Rs1\<rightarrow> []"
      by (simp add: ProductionStep_def Productions_def)
    from 15 have 16: "[NT N] -Rs1\<rightarrow>\<^sup>* []"
      by (meson ProducesInN.simps(1) ProducesInN.simps(2) Produces_def)
    from 11 and 16 have 17: "[] \<in> Language N Rs1"
      apply(unfold Language_def PartialEvalLanguage_def IsTerminalWord_def)
      by simp
    from 17 have 18: "[] \<in> DelAllNullableNTsFromElemList [NT N] Rs1"
      apply(unfold DelAllNullableNTsFromElemList_def DelNTFromElemListSet_def)
      by fastforce
    from 10 and 
      
    
      

  
 

(* Double induction yay, do it on the length of t now where A -Rs1\<rightarrow> t and t -Rs1\<rightarrow>^(n) x *)
lemma Del_Part2:
  assumes a: "transformDel G1 G2"
  assumes b: "\<And>m A x. (m \<le> n \<and> IsTerminalWord x \<and> x \<noteq> Nil \<and> [NT A] -(snd G1)\<rightarrow>\<^sup>m x \<Longrightarrow> [NT A] -(snd G2)\<rightarrow>\<^sup>* x)"
  assumes c: "ProducesInN [NT A] (snd G1) (n+1) x"
  assumes d: "IsTerminalWord x"
  shows      "[NT A] -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from a have 0: "\<exists> S Rs1 Rs2. 
                  (S, Rs1) = G1
                  \<and> (S, Rs2) = G2
                  \<and> Rs2 = RemoveAllEpsilonProds S (Rs1 \<union> DelAllNullableNTsFromRules Rs1)"
          (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformDel_def)
  then obtain S Rs1 Rs2 where r: "?P S Rs1 Rs2" by blast
  from r have e: "G1 = (S, Rs1)" by auto
  from r have f: "G2 = (S, Rs2)" by auto
  from r have g: "Rs2 = RemoveAllEpsilonProds S (Rs1 \<union> DelAllNullableNTsFromRules Rs1)" by auto
  from c and e have 1: "\<exists> rhs. ProducesInN rhs Rs1 n x \<and> [NT A] -Rs1\<rightarrow> rhs"
    (is "\<exists> rhs. ?P rhs")
    by auto
  then obtain rhs where 2: "?P rhs" by blast
  (* there exists a t' such that A -Rs2\<rightarrow> t' and t' -Rs2\<rightarrow>\<^sup>* x *)
  (* find that t' by induction on t ig *)

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
  where "finiteCFG G \<equiv> finite (snd G)"

lemma StartFinite:
  assumes a: "transformStart G1 S0 G2"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG G2"
proof-
  from a and b show ?thesis
    by (metis finiteCFG_def finite_insert snd_conv transformStart_def)
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
  fixes  Sk :: "'a set"
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
    by (metis finiteCFG_def finite_Diff finite_UnI snd_conv transformUnitSingle2_def)
qed

lemma listFinite:
  fixes      L :: "'a list"
  shows      "finite (set L)"
  by auto

definition RuleRhsSubset :: "('n, 't) Rule \<Rightarrow> ('n, 't) Rule \<Rightarrow> bool"
  where "RuleRhsSubset R1 R2 \<equiv> set (snd R1) \<subseteq> set (snd R2)" 

definition RuleRhsSize :: "('n, 't) Rule \<Rightarrow> ('n, 't) Rule \<Rightarrow> bool"
  where "RuleRhsSize R1 R2 \<equiv> size (snd R1) \<le> size (snd R2)" 

definition RuleLhsSame :: "('n, 't) Rule \<Rightarrow> ('n, 't) Rule \<Rightarrow> bool"
  where "RuleLhsSame R1 R2 \<equiv> fst R1 = fst R2" 

lemma DelFinite_Part1:
  fixes      H :: "(('n, 't) Rule \<times> ('n, 't) Rule) set" 
  assumes a: "H = {((S, l @ r), S, l @ NT N # r) | S l r. True}"
  assumes b: "(A, B) \<in> H"
  shows      "(RuleRhsSubset A B)"
proof-
  have 0: "\<And> l r a. (set (l @ r)) \<subseteq> (set (l @ a # r))"
    by (simp add: subsetI)
  from a and b have 1: "\<exists> S l r. A = (S, l @ r) \<and> B = (S, l @ NT N # r)" (is "\<exists> S l r. ?P S l r")
    by simp
  then obtain S l r where 2: "?P S l r" by blast
  from 2 and a show ?thesis
    by (unfold RuleRhsSubset_def, auto)
qed

lemma DelFinite_Part2:
  fixes      H :: "(('n, 't) Rule \<times> ('n, 't) Rule) set" 
  assumes a: "H = {((S, l @ r), S, l @ NT N # r) | S l r. True}"
  assumes b: "(A, B) \<in> H"
  shows      "(RuleRhsSize A B)"
proof-
  have 0: "\<And> l r a. (size (l @ r)) \<le> (size (l @ a # r))"
    by (simp add: subsetI)
  from a and b have 1: "\<exists> S l r. A = (S, l @ r) \<and> B = (S, l @ NT N # r)" (is "\<exists> S l r. ?P S l r")
    by simp
  then obtain S l r where 2: "?P S l r" by blast
  from 2 and a show ?thesis
    by (unfold RuleRhsSize_def, auto)
qed

lemma DelFinite_Part3:
  fixes      H :: "(('n, 't) Rule \<times> ('n, 't) Rule) set" 
  assumes a: "H = {((S, l @ r), S, l @ NT N # r) | S l r. True}"
  assumes b: "(A, B) \<in> H\<^sup>+"
  shows      "(RuleRhsSubset A B)"

proof-
  from a and DelFinite_Part1 have 1: "\<And>y. (A, y) \<in> H \<Longrightarrow> (RuleRhsSubset A) y"
    by (smt (verit, del_insts) mem_Collect_eq)
  from 1 have 2: "\<And>y z. (RuleRhsSubset y) z \<Longrightarrow> (RuleRhsSubset A) y \<Longrightarrow> (RuleRhsSubset A) z"
    by (simp add: RuleRhsSubset_def)
  from a and 2 have 3: "\<And>y z. (y, z) \<in> H \<Longrightarrow> (RuleRhsSubset A) y \<Longrightarrow> (RuleRhsSubset A) z"
    by (smt (verit, del_insts) DelFinite_Part1 mem_Collect_eq)
  from 1 and 3 and trancl_induct and b show ?thesis
    by (smt (verit, ccfv_SIG))
qed  


lemma DelFinite_Part4:
  fixes      H :: "(('n, 't) Rule \<times> ('n, 't) Rule) set" 
  assumes a: "H = {((S, l @ r), S, l @ NT N # r) | S l r. True}"
  assumes b: "(A, B) \<in> H\<^sup>+"
  shows      "(RuleRhsSize A B)"

proof-
  from a and DelFinite_Part2 have 1: "\<And>y. (A, y) \<in> H \<Longrightarrow> (RuleRhsSize A) y"
    by (smt (verit, del_insts) mem_Collect_eq)
  from 1 have 2: "\<And>y z. (RuleRhsSize y) z \<Longrightarrow> (RuleRhsSize A) y \<Longrightarrow> (RuleRhsSize A) z"
    by (simp add: RuleRhsSize_def)
  from a and 2 have 3: "\<And>y z. (y, z) \<in> H \<Longrightarrow> (RuleRhsSize A) y \<Longrightarrow> (RuleRhsSize A) z"
    by (smt (verit, del_insts) DelFinite_Part2 mem_Collect_eq)
  from 1 and 3 and trancl_induct and b show ?thesis
    by (smt (verit, ccfv_SIG))
qed  

lemma DelFinite_Part5:
  fixes      Rhs :: "('n, 't) Elem list"
  fixes      N :: "'n"
  fixes      S :: "'n"
  fixes      NR :: "('n, 't) Rule"
  assumes a: "(NR, (S, Rhs)) \<in> DelNTFromRuleSet N"
  shows      "NR = (S, Rhs) \<or> (NR, (S, Rhs)) \<in> {((S, l @ r), S, l @ NT N # r) | S l r. True}\<^sup>+"
proof-
  have 0: "\<And> a b L. (a, b) \<in> L\<^sup>* \<Longrightarrow> (a = b) \<or> (a, b) \<in> L\<^sup>+"
    by (metis rtranclD)
  from 0 and a show ?thesis
    by (unfold DelNTFromRuleSet_def, smt (verit, best) "0")
qed

lemma subsetListFinite:
  fixes      S :: "'a set"
  fixes      H :: "'a list set"
  fixes      n :: "nat"
  assumes a: "finite S"
  assumes b: "H = {L | L. (set L) \<subseteq> S \<and> (size L) \<le> n}"
  shows      "finite H"
  using a and b apply-
  apply(induction n)
   apply auto[1]
  using finite_lists_length_le by force

lemma DelFinite_Part6:
  fixes      H :: "(('n, 't) Rule \<times> ('n, 't) Rule) set" 
  assumes a: "H = {((S, l @ r), S, l @ NT N # r) | S l r. True}"
  assumes b: "(A, B) \<in> H"
  shows      "(RuleLhsSame A B)"
proof-
  from a and b have 1: "\<exists> S l r. A = (S, l @ r) \<and> B = (S, l @ NT N # r)" (is "\<exists> S l r. ?P S l r")
    by simp
  then obtain S l r where 2: "?P S l r" by blast
  from 2 and a show ?thesis
    by (unfold RuleLhsSame_def, auto)
qed


lemma DelFinite_Part7:
  fixes      H :: "(('n, 't) Rule \<times> ('n, 't) Rule) set" 
  assumes a: "H = {((S, l @ r), S, l @ NT N # r) | S l r. True}"
  assumes b: "(A, B) \<in> H\<^sup>+"
  shows      "(RuleLhsSame A B)"

proof-
  from a and DelFinite_Part6 have 1: "\<And>y. (A, y) \<in> H \<Longrightarrow> (RuleLhsSame A) y"
    by (smt (verit, del_insts) mem_Collect_eq)
  from 1 have 2: "\<And>y z. (RuleLhsSame y) z \<Longrightarrow> (RuleLhsSame A) y \<Longrightarrow> (RuleLhsSame A) z"
    by (simp add: RuleLhsSame_def)
  from a and 2 have 3: "\<And>y z. (y, z) \<in> H \<Longrightarrow> (RuleLhsSame A) y \<Longrightarrow> (RuleLhsSame A) z"
    by (smt (verit, del_insts) DelFinite_Part6 mem_Collect_eq)
  from 1 and 3 and trancl_induct and b show ?thesis
    by (smt (verit, ccfv_SIG))
qed  
  
  
lemma DelFinite_Part8:
  fixes      Rhs :: "('n, 't) Elem list"
  fixes      N :: "'n"
  fixes      S :: "'n"
  assumes a: "H = {NR | NR. (NR, (S, Rhs)) \<in> DelNTFromRuleSet N}"
  shows      "finite H"
proof-
  from a and DelFinite_Part5 have 0: "\<And> R. R \<in> H \<Longrightarrow> R = (S, Rhs) \<or> (R, (S, Rhs)) \<in> {((S, l @ r), S, l @ NT N # r) | S l r. True}\<^sup>+"
    by (smt (verit, del_insts) Collect_cong mem_Collect_eq)
  have 1: "\<And> R. (R, (S, Rhs)) \<in> 
          {((S, l @ r), S, l @ NT N # r) | S l r. True}\<^sup>+
          \<Longrightarrow> (RuleRhsSubset R) (S, Rhs)"
    by (simp add: DelFinite_Part3)
  have 2: "\<And> R. (R, (S, Rhs)) \<in> 
          {((S, l @ r), S, l @ NT N # r) | S l r. True}\<^sup>+
          \<Longrightarrow> (RuleRhsSize R) (S, Rhs)"
    by (simp add: DelFinite_Part4)
  from 1 and a and 0 have 3: "\<And> R. R \<in> H \<Longrightarrow> (RuleRhsSubset R) (S, Rhs)"
    apply(unfold DelNTFromRuleSet_def)
    using RuleRhsSubset_def by blast
  from 2 and a and 0 have 4: "\<And> R. R \<in> H \<Longrightarrow> (RuleRhsSize R) (S, Rhs)"
    apply(unfold DelNTFromRuleSet_def)
    using RuleRhsSize_def by blast
  from 3 have 5: "H \<subseteq> {R | R. (RuleRhsSubset R) (S, Rhs)}"
    by blast
  from 4 have 6: "H \<subseteq> {R | R. (RuleRhsSize R) (S, Rhs)}"
    by blast
  from listFinite have 7: "finite (set Rhs)"
    by simp
  have 8: "{(set Rhs1) | Rhs1. (RuleRhsSubset (S, Rhs1)) (S, Rhs)} \<subseteq> (Pow (set Rhs))"
    by(unfold RuleRhsSubset_def Pow_def, auto)
  from 8 and 5 have 9: "\<And> R. R \<in> H \<Longrightarrow> (set (snd R)) \<in> {(set Rhs1) | Rhs1. (RuleRhsSubset (S, Rhs1)) (S, Rhs)}"
    by (metis (mono_tags, lifting) "3" CollectI RuleRhsSubset_def snd_conv)
  from 9 and 8 have 10: "H \<subseteq> {S | S. (set (snd S)) \<subseteq> (set Rhs)}"
    by blast
  from 6 have 11 : "H \<subseteq> {S | S. (size (snd S)) \<le> (size Rhs)}"
    by (simp add: RuleRhsSize_def)
  from 10 and 11 have 12: "H \<subseteq> {S | S. (size (snd S)) \<le> (size Rhs) \<and> (set (snd S)) \<subseteq> (set Rhs)}"
    by auto
  from a and 0 have 13: "\<And> R. R \<in> H \<Longrightarrow> (fst R) = S"
    by (smt (verit, best) DelFinite_Part5 DelFinite_Part7 RuleLhsSame_def fstI mem_Collect_eq)
  from 13 and 12 have 14: "H \<subseteq> {(S, R) | R. (size R) \<le> (size Rhs) \<and> (set R) \<subseteq> (set Rhs)}"
    by auto
  have 15: "\<exists> n. size Rhs \<le> n" (is "\<exists> n. ?P n")
    by blast
  then obtain n where 16: "?P n" by blast
  from 16 and 14 have 17: "H \<subseteq> {(S, R) | R. (size R) \<le> n \<and> (set R) \<subseteq> (set Rhs)}"
    by auto
  from 17 and subsetListFinite and 7 have 18: "finite {R | R. (size R) \<le> n \<and> (set R) \<subseteq> (set Rhs)}"
    by(rule_tac S="set Rhs" in subsetListFinite, auto)
  have 19: "{(S, R) | R. (size R) \<le> n \<and> (set R) \<subseteq> (set Rhs)} = image (\<lambda> R. (S, R)) {R | R. (size R) \<le> n \<and> (set R) \<subseteq> (set Rhs)}"
    by (auto)
  from 19 and 18 and 17 and finiteImage show ?thesis
    by (simp add: finite_subset)
qed

lemma DelFinite_Part9:
  fixes      Rs1 :: "('n, 't) RuleSet"
  fixes      N :: "'n"
  assumes a: "finite Rs1"
  shows      "finite (DelNTFromRule N Rs1)"
proof-
  from DelFinite_Part8 have 0: "\<And> R. finite {NR | NR. (NR, R) \<in> DelNTFromRuleSet N}"
    apply(rule_tac N="N" and S="fst R" and Rhs="snd R" in DelFinite_Part8)
    by force
  have 1: "(DelNTFromRule N Rs1) \<subseteq> \<Union> {Rs | R Rs. R \<in> Rs1 \<and> Rs = {NR | NR. (NR, R) \<in> DelNTFromRuleSet N}}"
    by(unfold DelNTFromRule_def, auto)
  from 0 have 2: "\<And> R. R \<in> {Rs | R Rs. R \<in> Rs1 \<and> Rs = {NR | NR. (NR, R) \<in> DelNTFromRuleSet N}} \<Longrightarrow> finite R"
    by blast
  have 3: "{Rs | R Rs. R \<in> Rs1 \<and> Rs = {NR | NR. (NR, R) \<in> DelNTFromRuleSet N}}
           = image (\<lambda> R. {NR |NR. (NR, R) \<in> DelNTFromRuleSet N}) Rs1"
    by blast
  from a and 3 and finiteImage have 4: "finite {Rs | R Rs. R \<in> Rs1 \<and> Rs = {NR | NR. (NR, R) \<in> DelNTFromRuleSet N}}"
    by auto
  from 4 and 2 and finite_Union have 5: "finite (\<Union> {Rs | R Rs. R \<in> Rs1 \<and> Rs = {NR | NR. (NR, R) \<in> DelNTFromRuleSet N}})"
    by blast
  from 5 and 1 show ?thesis
    using finite_subset by auto
qed

lemma DelFinite_Part10:
  fixes      Rs1 :: "('n, 't) RuleSet"
  fixes      N :: "'n"
  assumes a: "[] \<in> Language N Rs1"
  shows      "\<exists> R. R \<in> Rs1 \<and> ProducingNT R = N"
proof-
  from a have 0: "\<exists> n. [NT N] -Rs1\<rightarrow>\<^sup>n []" (is "\<exists> n. ?P n")
    by (simp add: Language_def Produces_def)
  then obtain n where 1: "?P n" by blast
  from 1 show ?thesis
    by(induction n, auto)
qed

lemma DelFinite_Part11:
  fixes      Rs1 :: "('n, 't) RuleSet"
  assumes a: "finite Rs1"
  shows      "finite (DelAllNullableNTsFromRules Rs1)"
proof-
  from DelFinite_Part10 have 0: "\<And> N. [] \<in> Language N Rs1 \<Longrightarrow> \<exists> R. R \<in> Rs1 \<and> ProducingNT R = N"
    by (auto)
  from 0 have 1: "{N | N. [] \<in> Language N Rs1} \<subseteq> image ProducingNT Rs1"
    by auto
  from 1 have 2: "finite {N | N. [] \<in> Language N Rs1}"
    by (metis assms finite_surj)
  from 2 and finiteImage have 3: "{(DelNTFromRule N Rs1) | N. [] \<in> Language N Rs1}
                                 = image (\<lambda> N. (DelNTFromRule N Rs1)) {N | N. [] \<in> Language N Rs1}"
    by(auto)
  from 3 and 2 and finiteImage have 4: "finite {(DelNTFromRule N Rs1) | N. [] \<in> Language N Rs1}"
    by auto
  have 5: "DelAllNullableNTsFromRules Rs1 \<subseteq> \<Union>{(DelNTFromRule N Rs1) | N. [] \<in> Language N Rs1}"
    by(unfold DelAllNullableNTsFromRules_def, auto)
  from a and 4 and DelFinite_Part9 and finite_Union have 6: "finite (\<Union>{(DelNTFromRule N Rs1) | N. [] \<in> Language N Rs1})"
    apply(rule_tac A="{DelNTFromRule N Rs1 |N. [] \<in> \<lbrakk>N\<rbrakk>\<^sub>Rs1}" in finite_Union, auto)
    by (simp add: DelFinite_Part9)
  from 6 and 5 show ?thesis
    using finite_subset by blast
qed

lemma DelFinite:
  assumes a: "transformDel2 G1 G2"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG G2"
proof-
  have 0: "\<And> R S. RemoveAllEpsilonProds S R \<subseteq> R"
    by(unfold RemoveAllEpsilonProds_def, auto)
  from a and b and 0 show ?thesis
  apply (unfold transformDel2_def finiteCFG_def)
  using DelFinite_Part11 infinite_super by fastforce
qed

(* Measure for Term to prove that it terminates *)

fun CountTerminals :: "('n, 't) Elem list \<Rightarrow> nat"
  where "CountTerminals [] = 0" | 
        "CountTerminals ((T a) # xs) = 1 + CountTerminals xs" | 
        "CountTerminals ((NT a) # xs) = CountTerminals xs" 

fun CountNonSingleTerminals :: "('n, 't) Rule \<Rightarrow> nat"
  where "CountNonSingleTerminals (_, []) = 0" |
        "CountNonSingleTerminals (_, a # []) = 0" | 
        "CountNonSingleTerminals (_, El) = CountTerminals El"

definition TermFold :: "('n, 't) Rule \<Rightarrow> nat \<Rightarrow> nat"
  where "TermFold R N = N + (CountNonSingleTerminals R)"

definition TermRuleMeasure :: "('n, 't) RuleSet \<Rightarrow> nat"
  where "TermRuleMeasure R = Finite_Set.fold TermFold 0 R"

definition TermMeasure :: "('n, 't) CFG \<Rightarrow> nat"
  where "TermMeasure G = TermRuleMeasure (snd G)"

lemma CountProperty1:
  shows      "CountTerminals (L @ R) = CountTerminals L + CountTerminals R"
  apply(induction L, auto)
  by (smt (verit, best) CountTerminals.elims CountTerminals.simps(3) add.commute add_Suc_right list.distinct(1) list.sel(1) list.sel(3) plus_1_eq_Suc)

lemma CountProperty2:
  assumes a: "(L @ R \<noteq> [])"
  shows      "CountNonSingleTerminals (S1, L @ (T(a) # R)) = CountNonSingleTerminals (S2, L @ (NT(N) # R)) + 1"
proof-
  from a have 0: "CountNonSingleTerminals (S1, L @ (T(a) # R)) = CountTerminals (L @ (T(a) # R))"
    by (metis (no_types, opaque_lifting) CountNonSingleTerminals.simps(3) append_Cons append_Nil neq_Nil_conv)
  from a have 1: "CountNonSingleTerminals (S2, L @ (NT(N) # R)) =  CountTerminals (L @ (NT(N) # R))"
    by (metis (no_types, opaque_lifting) CountNonSingleTerminals.simps(3) append_Cons append_Nil neq_Nil_conv)
  have 2: "CountTerminals (L @ (T(a) # R)) = CountTerminals (L @ (NT(N) # R)) + 1"
    by (simp add: CountProperty1)
  from 0 and 1 and 2 show ?thesis
    by auto
qed

(*
lemma foldInsert:
  fixes      f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes      E :: "'a"
  fixes      Z :: "'b"
  assumes a: "comp_fun_commute_on (insert E S) f"
  assumes b: "finite S"
  assumes c: "E \<notin> S"
  shows      "Finite_Set.fold f Z (insert E S) = f E (Finite_Set.fold f Z S)"
proof-
  from b have 0: "finite (insert E S)"
    by blast
  have 1: "S \<subseteq> (insert E S)"
    by auto
  from 0 and 1 and b and a and c and comp_fun_commute_on.fold_insert show ?thesis
    apply (rule_tac S="(insert E S)" and f="f" and A="S" and x="E" and z="Z" in comp_fun_commute_on.fold_insert)
    apply meson
    apply force
    apply blast
    by blast
qed
*)

lemma TermTerminate_Part1:
  assumes a: "R1 = (S1, L @ T a # R)"
  assumes b: "R2 = (S1, L @ NT N # R)"
  assumes c: "R3 = (N, [T a])"
  assumes d: "(L @ R \<noteq> [])"
  assumes e: "G1 = (S, Rs1)"
  assumes f: "G2 = (S, Rs2)"
  assumes g: "R1 \<in> Rs1"
  assumes h: "finite Rs1"
  assumes i: "finite Rs2"
  assumes j: "Rs2 = {R2, R3} \<union> (Rs1 - {R1})"
  assumes k: "NT N \<notin> NonTerminals G1"
  shows      "TermMeasure G1 > TermMeasure G2"
proof-
  from c have "CountNonSingleTerminals R3 = 0" by simp
  from a and b and d have "CountNonSingleTerminals R1 = CountNonSingleTerminals R2 + 1"
    by (meson CountProperty2)
  
theorem TermTerminate:
  assumes a: "transformTermSingle G1 N G2"
  assumes b: "finiteCFG G1"
  shows      "TermMeasure G1 > TermMeasure G2"
proof-
  from a and b and TermFinite have 0: "finiteCFG G2" 
    by metis
  from a have 1: "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
                    (S, Rs1) = G1 
                    \<and> R1 = (S1, L @ (T(a) # R))
                    \<and> R2 = (S1, L @ (NT(N) # R))
                    \<and> R3 = (N, [T a])
                    \<and> (L @ R \<noteq> [])
                    \<and> (S, Rs2) = G2 
                    \<and> R1 \<in> Rs1
                    \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                    \<and> NT(N) \<notin> NonTerminals(G1)" 
                  (is "\<exists>S R1 R2 R3 Rs1 Rs2 S1 L R a. ?P S R1 R2 R3 Rs1 Rs2 S1 L R a")
    by (simp add: transformTermSingle_def)
  from 1 obtain S R1 R2 R3 Rs1 Rs2 S1 L R a where 2: "?P S R1 R2 R3 Rs1 Rs2 S1 L R a" by blast
  from 2 have 3: "CountNonSingleTerminals R3 = 0"
    by simp
  from 2 have 4: "CountNonSingleTerminals R1 = CountNonSingleTerminals R2 + 1"
    by (meson CountProperty2)
end
