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

definition equivLang :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "equivLang G1 G2 \<equiv> \<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"

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
  from 7 have 12: "\<exists> ln rn Nn rhs. [NT N] = ln @ [NT Nn] @ rn \<and> t = ln @ rhs @ rn \<and> (Nn, rhs) \<in> Rs" 
    (is "\<exists> ln rn Nn rhs. ?P  ln rn Nn rhs")
    apply(unfold ProductionStep_def Productions_def) 
    by blast
  then obtain ln rn Nn rhs where 13: "?P ln rn Nn rhs" by blast
  from 13 have 14: "ln = [] \<and> rn = [] \<and> Nn = N \<and> rhs = t"
    by (simp add: Cons_eq_append_conv)
  from 14 13 have 15: "(N, t) \<in> Rs" by auto
  from 11 and 15 show ?thesis by auto
qed

section "Transforms Definition"

definition transformStartTest :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool" 
  where "transformStartTest G1 S0 G2 \<equiv> \<exists> S1 R1 R2. (S1, R1) = G1 
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

lemma Start_Part2:
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

lemma Start_Part3:
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
    by (metis Start_Part2 a c d)
  from 0 and g show ?thesis
    by blast
qed

lemma Start_Part4:
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
    by (metis Start_Part3 a c d)
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

theorem verifyTransformStartTest:
  assumes a: "transformStartTest G1 S0 G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 1: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (metis Start_Part1 transformStartTest_def)  
  from a have 2: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (metis Start_Part4 transformStartTest_def)
  from 1 and 2 show ?thesis
    by blast
qed

definition transformTermTest :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformTermTest G1 N G2 \<equiv> \<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
                                 (S, Rs1) = G1 
                                 \<and> R1 = (S1, L @ (T(a) # R))
                                 \<and> R2 = (S1, L @ (NT(N) # R))
                                 \<and> R3 = (N, [T a])
                                 \<and> (L @ R \<noteq> [])
                                 \<and> (S, Rs2) = G2 
                                 \<and> R1 \<in> Rs1
                                 \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                                 \<and> NT(N) \<notin> NonTerminals(G1)"

lemma Term_Part1:
  assumes p: "transformTermTest G1 N G2"
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
    by (simp add: transformTermTest_def)
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

lemma Term_Part2:
  fixes      A :: "('n, 't) Elem list"
  fixes      G1 :: "('n, 't) CFG"
  assumes p: "transformTermTest G1 N G2"
  assumes l: "(NT N) \<notin> set A" 
  assumes m: "A -(snd G1)\<rightarrow>\<^sup>n x"
  shows      "A -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from p and l and Term_Part1 have 0: "\<And>A x. (NT N \<notin> set A \<and> A -snd G1\<rightarrow>\<^sup>n x \<Longrightarrow> A -snd G2\<rightarrow>\<^sup>* x)"
    apply (induction n)
    apply (metis ProducesInN.simps(1) Produces_def)
    by (smt (verit) Term_Part1)
  from 0 and m and l show ?thesis
    by blast
qed
  
lemma Term_Part3:
  assumes a: "transformTermTest G1 N G2"
  assumes b: "x \<in> \<lbrakk>G1\<rbrakk>"
  shows      "x \<in> \<lbrakk>G2\<rbrakk>"
proof-
  from b have 0: "\<exists> n S Rs1. [NT S] -Rs1\<rightarrow>\<^sup>n x \<and> (S, Rs1) = G1" (is "\<exists> n S Rs1. ?P n S Rs1")
    by (simp add: Language_def Lang_def Produces_def PartialEvalLanguage_def, auto)
  then obtain n S Rs1 where 1: "?P n S Rs1" by blast
  from Term_Part2 and a have 2: "\<And>A B x n. ((NT N) \<notin> set A \<and> A -(snd G1)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G2)\<rightarrow>\<^sup>* x)"
    by metis
  from a have 3: "NT N \<notin> NonTerminals G1"
    by(unfold transformTermTest_def, auto)
  from 1 and 3 have 4: "N \<noteq> S"
    by(unfold NonTerminals_def, auto)
  from 4 have 5: "NT N \<notin> set ([NT S])"
    by simp
  from 5 and 2 and 1 have 6: "[NT S] -(snd G2)\<rightarrow>\<^sup>* x"
    by force
  from a and 1 have 7: "\<exists> Rs2. G2 = (S, Rs2)" (is "\<exists> Rs2. ?P Rs2")
    by(unfold transformTermTest_def, blast)
  then obtain Rs2 where 8: "?P Rs2" by blast
  from b have 9: "IsTerminalWord x" 
    by (unfold Lang_def Language_def PartialEvalLanguage_def, auto)
  from 8 and 6 and 9 show ?thesis
    by (unfold Lang_def Language_def PartialEvalLanguage_def, auto)
qed

lemma Term_Part4:
  assumes a: "transformTermTest G1 N G2"
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
    by (simp add: transformTermTest_def)
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

lemma Term_Part5:
  assumes a: "transformTermTest G1 N G2"
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
    from 2 and 3 and p and a and b and Term_Part4 show ?thesis
      by (metis (no_types, lifting))      
  next
    assume y: "n = 0"
    from d and y have 0: "x = A"
      by simp
    from 0 show ?thesis
      by (meson ProducesInN.simps(1) Produces_def)
  qed
qed

lemma Term_Part6:
  fixes      A :: "('n, 't) Elem list"
  fixes      G1 :: "('n, 't) CFG"
  assumes p: "transformTermTest G1 N G2"
  assumes l: "(NT N) \<notin> set A" 
  assumes k: "IsTerminalWord x"
  assumes m: "A -(snd G2)\<rightarrow>\<^sup>n x"
  shows      "A -(snd G1)\<rightarrow>\<^sup>* x"
proof-
  have 0: "\<And>A x. IsTerminalWord x \<and> (NT N) \<notin> set A \<and> A -(snd G2)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x"
    apply (induction n rule: less_induct)
    by (smt (verit, best) Term_Part5 p)
  from 0 and p and l and m and k show ?thesis 
    by simp
qed

lemma Term_Part7:
  assumes a: "transformTermTest G1 N G2"
  assumes b: "x \<in> \<lbrakk>G2\<rbrakk>"
  shows      "x \<in> \<lbrakk>G1\<rbrakk>"
proof-
  from b have 0: "\<exists> n S Rs2. [NT S] -Rs2\<rightarrow>\<^sup>n x \<and> (S, Rs2) = G2" (is "\<exists> n S Rs2. ?P n S Rs2")
    by (simp add: Language_def Lang_def Produces_def PartialEvalLanguage_def, auto)
  then obtain n S Rs2 where 1: "?P n S Rs2" by blast
  from Term_Part6 and a have 2: "\<And>A B x n. ((NT N) \<notin> set A \<and> IsTerminalWord x \<and> A -(snd G2)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
    by metis
  from a have 3: "NT N \<notin> NonTerminals G1"
    by(unfold transformTermTest_def, auto)
  from a and 1 and 3 have 4: "N \<noteq> S"
    by (unfold NonTerminals_def transformTermTest_def, auto)
  from 4 have 5: "NT N \<notin> set ([NT S])"
    by simp
  from b have 6: "IsTerminalWord x"
    by (simp add: Lang_def Language_def PartialEvalLanguage_def)
  from 5 and 2 and 1 and 6 have 7: "[NT S] -(snd G1)\<rightarrow>\<^sup>* x"
    by force
  from a and 1 have 8: "\<exists> Rs1. G1 = (S, Rs1)" (is "\<exists> Rs1. ?P Rs1")
    by(unfold transformTermTest_def, auto)
  then obtain Rs1 where 9: "?P Rs1" by blast
  from 9 and 7 and 6 show ?thesis
    by(unfold Lang_def Language_def PartialEvalLanguage_def, auto)
qed

theorem verifyTransformTermTest: 
  assumes a: "transformTermTest G1 N G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (simp add: Term_Part3)
  from a have 1: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (simp add: Term_Part7)
  from 0 and 1 show ?thesis
    by fastforce
qed

definition transformBinTest :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformBinTest G1 N G2 \<equiv> \<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
                                   (S, Rs1) = G1 
                                 \<and> R1 = (S1, L @ a # R)
                                 \<and> R2 = (S1, L @ [NT N])
                                 \<and> R3 = (N, a # R)  
                                 \<and> L \<noteq> [] \<and> R \<noteq> []
                                 \<and> (S, Rs2) = G2 
                                 \<and> R1 \<in> Rs1
                                 \<and> Rs2 = {R2, R3} \<union> (Rs1 - {R1})
                                 \<and> NT(N) \<notin> NonTerminals(G1)"

lemma Bin_Part1:
  assumes p: "transformBinTest G1 N G2"
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
    by (simp add: transformBinTest_def)
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


lemma Bin_Part2:
  fixes      A :: "('n, 't) Elem list"
  fixes      G1 :: "('n, 't) CFG"
  assumes p: "transformBinTest G1 N G2"
  assumes l: "(NT N) \<notin> set A" 
  assumes m: "A -(snd G1)\<rightarrow>\<^sup>n x"
  shows      "A -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from p and l and Bin_Part1 have 0: "\<And>A x. (NT N \<notin> set A \<and> A -snd G1\<rightarrow>\<^sup>n x \<Longrightarrow> A -snd G2\<rightarrow>\<^sup>* x)"
    apply (induction n)
    apply (metis ProducesInN.simps(1) Produces_def)
    by (smt (verit) Bin_Part1)
  from 0 and m and l show ?thesis
    by blast
qed

lemma Bin_Part3:
  assumes a: "transformBinTest G1 N G2"
  assumes b: "x \<in> \<lbrakk>G1\<rbrakk>"
  shows      "x \<in> \<lbrakk>G2\<rbrakk>"
proof-
  from b have 0: "\<exists> n S Rs1. [NT S] -Rs1\<rightarrow>\<^sup>n x \<and> (S, Rs1) = G1" (is "\<exists> n S Rs1. ?P n S Rs1")
    by (simp add: Language_def Lang_def Produces_def PartialEvalLanguage_def, auto)
  then obtain n S Rs1 where 1: "?P n S Rs1" by blast
  from Bin_Part2 and a have 2: "\<And>A B x n. ((NT N) \<notin> set A \<and> A -(snd G1)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G2)\<rightarrow>\<^sup>* x)"
    by metis
  from a have 3: "NT N \<notin> NonTerminals G1"
    by(unfold transformBinTest_def, auto)
  from 1 and 3 have 4: "N \<noteq> S"
    by(unfold NonTerminals_def, auto)
  from 4 have 5: "NT N \<notin> set ([NT S])"
    by simp
  from 5 and 2 and 1 have 6: "[NT S] -(snd G2)\<rightarrow>\<^sup>* x"
    by force
  from a and 1 have 7: "\<exists> Rs2. G2 = (S, Rs2)" (is "\<exists> Rs2. ?P Rs2")
    by(unfold transformBinTest_def, blast)
  then obtain Rs2 where 8: "?P Rs2" by blast
  from b have 9: "IsTerminalWord x" 
    by (unfold Lang_def Language_def PartialEvalLanguage_def, auto)
  from 8 and 6 and 9 show ?thesis
    by (unfold Lang_def Language_def PartialEvalLanguage_def, auto)
qed

lemma Bin_Part4:
  assumes a: "transformBinTest G1 N G2"
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
    by (simp add: transformBinTest_def)
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

lemma Bin_Part5:
  assumes a: "transformBinTest G1 N G2"
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
    from 2 and 3 and p and a and b and Bin_Part4 show ?thesis
      by (metis (no_types, lifting))      
  next
    assume y: "n = 0"
    from d and y have 0: "x = A"
      by simp
    from 0 show ?thesis
      by (meson ProducesInN.simps(1) Produces_def)
  qed
qed

lemma Bin_Part6:
  fixes      A :: "('n, 't) Elem list"
  fixes      G1 :: "('n, 't) CFG"
  assumes p: "transformBinTest G1 N G2"
  assumes l: "(NT N) \<notin> set A" 
  assumes k: "IsTerminalWord x"
  assumes m: "A -(snd G2)\<rightarrow>\<^sup>n x"
  shows      "A -(snd G1)\<rightarrow>\<^sup>* x"
proof-
  have 0: "\<And>A x. IsTerminalWord x \<and> (NT N) \<notin> set A \<and> A -(snd G2)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x"
    apply (induction n rule: less_induct)
    by (smt (verit, best) Bin_Part5 p)
  from 0 and p and l and m and k show ?thesis 
    by simp
qed

lemma Bin_Part7:
  assumes a: "transformBinTest G1 N G2"
  assumes b: "x \<in> \<lbrakk>G2\<rbrakk>"
  shows      "x \<in> \<lbrakk>G1\<rbrakk>"
proof-
  from b have 0: "\<exists> n S Rs2. [NT S] -Rs2\<rightarrow>\<^sup>n x \<and> (S, Rs2) = G2" (is "\<exists> n S Rs2. ?P n S Rs2")
    by (simp add: Language_def Lang_def Produces_def PartialEvalLanguage_def, auto)
  then obtain n S Rs2 where 1: "?P n S Rs2" by blast
  from Bin_Part6 and a have 2: "\<And>A B x n. ((NT N) \<notin> set A \<and> IsTerminalWord x \<and> A -(snd G2)\<rightarrow>\<^sup>n x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
    by metis
  from a have 3: "NT N \<notin> NonTerminals G1"
    by(unfold transformBinTest_def, auto)
  from a and 1 and 3 have 4: "N \<noteq> S"
    by (unfold NonTerminals_def transformBinTest_def, auto)
  from 4 have 5: "NT N \<notin> set ([NT S])"
    by simp
  from b have 6: "IsTerminalWord x"
    by (simp add: Lang_def Language_def PartialEvalLanguage_def)
  from 5 and 2 and 1 and 6 have 7: "[NT S] -(snd G1)\<rightarrow>\<^sup>* x"
    by force
  from a and 1 have 8: "\<exists> Rs1. G1 = (S, Rs1)" (is "\<exists> Rs1. ?P Rs1")
    by(unfold transformBinTest_def, auto)
  then obtain Rs1 where 9: "?P Rs1" by blast
  from 9 and 7 and 6 show ?thesis
    by(unfold Lang_def Language_def PartialEvalLanguage_def, auto)
qed

theorem verifyTransformBinTest: 
  assumes a: "transformBinTest G1 N G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (simp add: Bin_Part3)
  from a have 1: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (simp add: Bin_Part7)
  from 0 and 1 show ?thesis
    by fastforce
qed


(* This definition doesn't terminate *)
(*
definition transformDelTest :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformDelTest G1 N G2 \<equiv> \<exists> S Rs1 Rs2. 
                                N \<noteq> S 
                                \<and> (S, Rs1) = G1
                                \<and> (S, Rs2) = G2
                                \<and> (N, Nil) \<in> Rs1
                                \<and> Rs2 = (DelNTFromRule N Rs1) - {(N, Nil)}"

definition NewUnitTransRuleSet :: "'n \<Rightarrow> 'n \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> ('n, 't) RuleSet"
  where "NewUnitTransRuleSet A B R1 \<equiv> {R2 | R2 Rhs. (B, Rhs) \<in> R1 \<and> (A, Rhs) = R2}"

definition transformUnitTest :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformUnitTest G1 A B G2 \<equiv> \<exists> S Rs1 Rs2. 
                                   (S, Rs1) = G1
                                   \<and> (S, Rs2) = G2
                                   \<and> (A, [NT(B)]) \<in> Rs1
                                   \<and> Rs2 = (Rs1 \<union> (NewUnitTransRuleSet A B Rs1)) - {(A, [NT(B)])}"
*)

    
definition IsUnitProductionRule :: "('n, 't) Rule \<Rightarrow> bool"
  where "IsUnitProductionRule R \<equiv> \<exists> N. (snd R) = [NT N]"

definition HasUnitProductionRule :: "('n, 't) RuleSet \<Rightarrow> 'n \<Rightarrow> bool"
  where "HasUnitProductionRule Rs N \<equiv> \<exists> R. R \<in> Rs \<and> (fst R) = N \<and> IsUnitProductionRule R"

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

definition transformUnitTest :: "('n, 't) CFG \<Rightarrow> 'n \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformUnitTest G1 A G2 \<equiv> \<exists> S Rs1 Rs2. 
                                   (S, Rs1) = G1
                                   \<and> (S, Rs2) = G2
                                   \<and> HasUnitProductionRule Rs1 A
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
  assumes a: "transformUnitTest G1 N G2"
  assumes b: "\<And>m A x. (m \<le> n \<and> IsTerminalWord x \<and> A -(snd G1)\<rightarrow>\<^sup>m x \<Longrightarrow> A -(snd G2)\<rightarrow>\<^sup>* x)"
  assumes c: "ProducesInN A (snd G1) (Suc n) x"
  assumes d: "IsTerminalWord x"
  shows      "A -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from a have 0: "\<exists> S Rs1 Rs2. 
                  (S, Rs1) = G1
                  \<and> (S, Rs2) = G2
                  \<and> HasUnitProductionRule Rs1 N
                  \<and> Rs2 = (Rs1 \<union> (NewUnitTransRuleSet N Rs1)) - (NTToNTSetForA N)"
          (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformUnitTest_def)
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
  assumes a: "transformUnitTest G1 N G2"
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
  assumes a: "transformUnitTest G1 N G2"
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
  assumes a: "transformUnitTest G1 N G2"
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
    by(simp add: transformUnitTest_def Lang_def Language_def PartialEvalLanguage_def, force)
qed

lemma Unit_Part9:
  assumes a: "transformUnitTest G1 N G2"
  assumes b: "\<And>A x. (IsTerminalWord x \<and> ProducesInN A (snd G2) n x \<Longrightarrow> A -(snd G1)\<rightarrow>\<^sup>* x)"
  assumes c: "ProducesInN A (snd G2) (Suc n) x"
  assumes d: "IsTerminalWord x"
  shows      "A -(snd G1)\<rightarrow>\<^sup>* x"
proof-
  from a have 0: "\<exists> S Rs1 Rs2. 
                  (S, Rs1) = G1
                  \<and> (S, Rs2) = G2
                  \<and> HasUnitProductionRule Rs1 N
                  \<and> Rs2 = (Rs1 \<union> (NewUnitTransRuleSet N Rs1)) - (NTToNTSetForA N)"
          (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformUnitTest_def)
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
  assumes a: "transformUnitTest G1 N G2"
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
  assumes a: "transformUnitTest G1 N G2"
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
    by(simp add: transformUnitTest_def Lang_def Language_def PartialEvalLanguage_def, force)
qed

lemma verifyTransformUnitTest:
  assumes a: "transformUnitTest G1 N G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (simp add: Unit_Part8)
  from a have 1: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (simp add: Unit_Part11)
  from 0 and 1 show ?thesis
    by fastforce
qed

definition DelSingleNullableNTFromElemListSet :: "('n, 't) RuleSet \<Rightarrow> (('n, 't) Elem list \<times> ('n, 't) Elem list) set"
  where "DelSingleNullableNTFromElemListSet Rs \<equiv> {((l @ r), (l @ NT(N) # r)) | l r N. [] \<in> Language N Rs}"

definition DelSingleNullableNTFromElemList :: "('n, 't) RuleSet \<Rightarrow> ('n, 't) Elem list \<Rightarrow> ('n, 't) Elem list \<Rightarrow> bool"
  where "DelSingleNullableNTFromElemList Rs E1 E2 \<equiv> (E2, E1) \<in> DelSingleNullableNTFromElemListSet Rs"

fun DelNullableNTsFromElemListInN :: "('n, 't) RuleSet \<Rightarrow> nat \<Rightarrow> ('n, 't) Elem list \<Rightarrow> ('n, 't) Elem list \<Rightarrow> bool"
  where "DelNullableNTsFromElemListInN Rs 0 E1 E2 = (E1 = E2)" |
        "DelNullableNTsFromElemListInN Rs (Suc n) E1 E2 = (\<exists> t. DelSingleNullableNTFromElemList Rs E1 t \<and> DelNullableNTsFromElemListInN Rs n t E2)"

definition DelNullableNTsFromElemList :: "('n, 't) RuleSet  \<Rightarrow> ('n, 't) Elem list \<Rightarrow> ('n, 't) Elem list \<Rightarrow> bool"
  where "DelNullableNTsFromElemList Rs E1 E2 \<equiv> \<exists> n. DelNullableNTsFromElemListInN Rs n E1 E2" 

definition DelNullableNTsFromRule :: "('n, 't) RuleSet \<Rightarrow> ('n, 't) Rule \<Rightarrow> ('n, 't) Rule \<Rightarrow> bool"
  where "DelNullableNTsFromRule Rs R1 R2 \<equiv> \<exists> N rhs1 rhs2. R1 = (N, rhs1) \<and> R2 = (N, rhs2) \<and> DelNullableNTsFromElemList Rs rhs1 rhs2"

definition DelAllNullableNTsFromRules :: "('n, 't) RuleSet \<Rightarrow> ('n, 't) RuleSet"
  where "DelAllNullableNTsFromRules X = { NR | NR OR. OR \<in> X \<and> DelNullableNTsFromRule X OR NR}"

definition RemoveAllEpsilonProds :: "'n \<Rightarrow> ('n, 't) RuleSet \<Rightarrow> ('n, 't) RuleSet"
  where "RemoveAllEpsilonProds S X = {R | R N Rhs. R \<in> X \<and> (N, Rhs) = R \<and> (N = S \<or> Rhs \<noteq> Nil)}"

definition transformDelTest :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "transformDelTest G1 G2 \<equiv> \<exists> S Rs1 Rs2.
                               (S, Rs1) = G1
                               \<and> (S, Rs2) = G2
                               \<and> Rs2 = RemoveAllEpsilonProds S (DelAllNullableNTsFromRules Rs1)"

lemma Del_Part1:
  assumes a: "DelNullableNTsFromElemListInN N n1 A B"
  assumes b: "DelNullableNTsFromElemListInN N n2 B C"
  shows      "DelNullableNTsFromElemListInN N (n1 + n2) A C"
proof-
  have 0: "\<And> A B C m. DelNullableNTsFromElemListInN N n1 A B \<and> DelNullableNTsFromElemListInN N m B C \<Longrightarrow> DelNullableNTsFromElemListInN N (n1+m) A C"
    apply(induction n1)
    apply simp
    by auto
  from a and b and 0 show ?thesis
    by force
qed

lemma Del_Part2:
  assumes a: "DelNullableNTsFromElemList N A B"
  assumes b: "DelNullableNTsFromElemList N B C"
  shows      "DelNullableNTsFromElemList N A C"
proof-
  from a and b and Del_Part1 show ?thesis
    apply(unfold DelNullableNTsFromElemList_def)
    by fastforce
qed

lemma Del_Part3:
  assumes a: "(DelSingleNullableNTFromElemList Rs) a b"
  shows      "(DelNullableNTsFromElemList Rs) a b"
proof-
  from a show ?thesis
    by (meson DelNullableNTsFromElemListInN.simps(1) DelNullableNTsFromElemListInN.simps(2) DelNullableNTsFromElemList_def)
qed

lemma Del_Part4:
  assumes a: "(DelSingleNullableNTFromElemList Rs) (l @ r) X"
  shows      "(\<exists> l'. (DelSingleNullableNTFromElemList Rs) l l' \<and> X = l' @ r) \<or> (\<exists> r'. (DelSingleNullableNTFromElemList Rs) r r' \<and> X = l @ r')"   
proof-
  from a have 0: "\<exists>a b N. l @ r = (a @ [NT N] @ b) \<and> X = (a @ b) \<and> [] \<in> Language N Rs" (is "\<exists> a b N. ?P a b N")
    by(unfold DelSingleNullableNTFromElemList_def DelSingleNullableNTFromElemListSet_def, auto) 
  then obtain a b N where 1: "?P a b N" by blast
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
    from 10 and 1 have 11: "(DelSingleNullableNTFromElemList Rs) l (a @ c)"
      apply(unfold DelSingleNullableNTFromElemList_def, auto) 
      using DelSingleNullableNTFromElemList_def DelSingleNullableNTFromElemListSet_def by fastforce
    from 10 and 1 have 12: "c @ r = b" by simp
    from 1 and 12 and 11 have 13: "\<exists> l'. (DelSingleNullableNTFromElemList Rs) l l' \<and> X = l' @ r"
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
    from 10 and 1 have 11: "(DelSingleNullableNTFromElemList Rs) r (c @ b)"
      apply(unfold DelSingleNullableNTFromElemList_def, auto) 
      using DelSingleNullableNTFromElemList_def DelSingleNullableNTFromElemListSet_def by fastforce
    from 10 and 1 have 12: "l @ c = a" by simp
    from 1 and 12 and 11 have 13: "\<exists> r'. (DelSingleNullableNTFromElemList Rs) r r' \<and> X = l @ r'"
      by force
    show ?thesis
      by (simp add: "13")
  qed
qed  

lemma Del_Part5:    
  assumes a: "\<And>l r. (DelNullableNTsFromElemListInN Rs n (l @ r) X) \<Longrightarrow> (\<exists>l' r'. DelNullableNTsFromElemList Rs l l' \<and> DelNullableNTsFromElemList Rs r r' \<and> l' @ r' = X)"
  assumes b: "DelNullableNTsFromElemListInN Rs (n+1) (l@r) X"
  shows      "\<exists>l' r'. DelNullableNTsFromElemList Rs l l' \<and> DelNullableNTsFromElemList Rs r r' \<and> l' @ r' = X"
proof-
  from b have 0: "\<exists> q. DelSingleNullableNTFromElemList Rs (l@r) q \<and> DelNullableNTsFromElemListInN Rs n q X" (is "\<exists> q. ?P q")
    by auto  
  then obtain q where 1 : "?P q" by blast
  from 1 and Del_Part4 have 2:"(\<exists> l'. DelSingleNullableNTFromElemList Rs l l' \<and> l' @ r = q) \<or> (\<exists> r'. DelSingleNullableNTFromElemList Rs r r' \<and> l @ r' = q)"
    by metis
  have 3: "\<And> x. DelNullableNTsFromElemListInN Rs 0 x x" 
    by simp
  from 3 have 4: "\<And> x. DelNullableNTsFromElemList Rs x x" 
    using DelNullableNTsFromElemList_def by metis
  from 1 have 5: "\<exists>l1 r1. DelNullableNTsFromElemList Rs l l1 \<and> DelNullableNTsFromElemList Rs r r1 \<and> l1 @ r1 = q" (is "\<exists> l1 r1. ?P l1 r1")
    using "2" "4" Del_Part3 by blast
  then obtain l1 r1 where 6: "?P l1 r1" by blast
  from 1 and 6 have 7: "DelNullableNTsFromElemListInN Rs n (l1@r1) X"
    by blast
  from a and 7 have 8: "\<exists>l' r'. DelNullableNTsFromElemList Rs l1 l' \<and> DelNullableNTsFromElemList Rs r1 r' \<and> l' @ r' = X" (is "\<exists> l' r'. ?P l' r'")
    by blast
  then obtain l' r' where 9: "?P l' r'" by blast
  from 9 and 6 and 2 show ?thesis
    by (metis Del_Part2)
qed

lemma Del_Part6:
  assumes a: "DelNullableNTsFromElemList Rs (l @ r) X"
  shows      "\<exists> l' r'. DelNullableNTsFromElemList Rs l l' \<and> DelNullableNTsFromElemList Rs r r' \<and> l' @ r' = X"
proof-
  from a have 0: "\<exists> n. DelNullableNTsFromElemListInN Rs n (l @ r) X" (is "\<exists> n. ?P n")
    by (simp add: DelNullableNTsFromElemList_def)
  then obtain n where 1: "?P n" by blast
  have 2: "\<And> l r. (DelNullableNTsFromElemListInN Rs n (l @ r) X) \<Longrightarrow> (\<exists>l' r'. DelNullableNTsFromElemList Rs l l' \<and> DelNullableNTsFromElemList Rs r r' \<and> l' @ r' = X)"
    apply(induction n)
     apply (meson DelNullableNTsFromElemListInN.simps(1) DelNullableNTsFromElemList_def)
    by (smt (verit, ccfv_threshold) Del_Part5 One_nat_def add.right_neutral add_Suc_right)
  from 2 and 1 show ?thesis
    by force
qed

lemma Del_Part7:
  assumes a: "transformDelTest G1 G2"
  assumes b: "[NT A] -(snd G1)\<rightarrow> rhs"
  assumes c: "rhs' \<noteq> Nil"
  assumes d: "DelNullableNTsFromElemList (snd G1) rhs rhs'"
  shows      "(A, rhs') \<in> (snd G2)"
proof-
  from a have 0: "\<exists> S Rs1 Rs2. 
                  (S, Rs1) = G1
                  \<and> (S, Rs2) = G2
                  \<and> Rs2 = RemoveAllEpsilonProds S (DelAllNullableNTsFromRules Rs1)"
          (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformDelTest_def)
  then obtain S Rs1 Rs2 where 1: "?P S Rs1 Rs2" by blast
  from c have 2: "\<And> H. (A, rhs') \<in> H \<Longrightarrow> (A, rhs') \<in> RemoveAllEpsilonProds S H"
    apply(unfold RemoveAllEpsilonProds_def) 
    by blast
  from b have 3: "(A, rhs) \<in> Rs1"
    by (smt (verit, ccfv_threshold) "1" CollectD Elem.inject(1) Nil_is_append_conv Pair_inject
        ProductionStep_def Productions_def append_eq_Cons_conv append_self_conv append_self_conv2 list.inject sndI)
  from d have 4: "(A, rhs') \<in> (DelAllNullableNTsFromRules Rs1)" 
    apply(unfold DelAllNullableNTsFromRules_def DelNullableNTsFromRule_def)
    using "1" "3" by force
  from 3 and 2 have 5: "(A, rhs') \<in> Rs2"
    using "1" "4" by blast
  from 5 and 1 show ?thesis
    by force
qed

lemma Del_Part8:
  assumes a: "DelSingleNullableNTFromElemList Rs a a'"
  shows      "DelSingleNullableNTFromElemList Rs (l@a@r) (l@a'@r)"
proof-
  from a show ?thesis
    apply(unfold DelSingleNullableNTFromElemList_def DelSingleNullableNTFromElemListSet_def)
    by (smt (verit, best) append.assoc append_Cons mem_Collect_eq prod.inject)
qed

lemma Del_Part9:
  assumes a: "DelNullableNTsFromElemListInN Rs n a a'"
  shows      "DelNullableNTsFromElemListInN Rs n (l@a@r) (l@a'@r)"
proof-
  have 0: "\<And> N a a'. DelNullableNTsFromElemListInN Rs n a a' \<Longrightarrow> DelNullableNTsFromElemListInN Rs n (l@a@r) (l@a'@r)"
    apply(induction n)
     apply auto[1]
    by (meson Del_Part8 DelNullableNTsFromElemListInN.simps(2))
  from 0 show ?thesis
    using assms by blast
qed

lemma Del_Part10:
  assumes a: "DelNullableNTsFromElemList Rs a a'"
  shows      "DelNullableNTsFromElemList Rs (l@a@r) (l@a'@r)"
proof-
  from a have 0: "\<exists> n. DelNullableNTsFromElemListInN Rs n a a'" (is "\<exists>n. ?P n")
    by (simp add: DelNullableNTsFromElemList_def)
  then obtain n where 1: "?P n" by blast
  from 1 have 2: "DelNullableNTsFromElemListInN Rs n (l@a@r) (l@a'@r)"
    by (simp add: Del_Part9)
  from 2 show ?thesis
    by (simp add: DelNullableNTsFromElemList_def, auto)
qed

lemma Del_Part11:
  assumes a: "DelNullableNTsFromElemList Rs l l'"
  assumes b: "DelNullableNTsFromElemList Rs r r'"
  shows      "DelNullableNTsFromElemList Rs (l@r) (l'@r')"
proof-
  from a have 0: "DelNullableNTsFromElemList Rs (l@r) (l'@r)"
    by (metis Del_Part10 append_self_conv2)
  from 0 and b have 1: "DelNullableNTsFromElemList Rs (l'@r) (l'@r')"
    by (metis Del_Part10 append.right_neutral)
  from 0 and 1 show ?thesis
    by (meson Del_Part2)
qed

lemma Del_Part12:
  assumes a: "DelNullableNTsFromElemList Rs [] a"
  shows      "a = []"
proof-
  have 0: "\<And> a. \<not> DelSingleNullableNTFromElemList Rs [] a"
    apply(unfold DelSingleNullableNTFromElemList_def DelSingleNullableNTFromElemListSet_def)
    by auto
  from a have 1: "\<exists> n. DelNullableNTsFromElemListInN Rs n [] a"(is "\<exists> n. ?P n")
    by (simp add: DelNullableNTsFromElemList_def)
  then obtain n where 2: "?P n" by blast  
  from 2 and 0 show ?thesis
    by(induction n, auto)
qed

lemma Del_Part13:
  assumes a: "(\<And>a a'. DelNullableNTsFromElemListInN Rs n a a' \<Longrightarrow> a -Rs\<rightarrow>\<^sup>* a')" 
  assumes b: "DelNullableNTsFromElemListInN Rs (Suc n) a a'"
  shows      "a -Rs\<rightarrow>\<^sup>* a'"
proof-
  from b have 0: "\<exists> t. DelSingleNullableNTFromElemList Rs a t \<and> DelNullableNTsFromElemListInN Rs n t a'" (is "\<exists> t. ?P t")
    by simp
  then obtain t where 1: "?P t" by blast
  from 1 and a have 2: "t -Rs\<rightarrow>\<^sup>* a'" by blast
  from 1 have 3: "DelSingleNullableNTFromElemList Rs a t"
    by blast
  from 3  have 4: "a -Rs\<rightarrow>\<^sup>* t"
    apply(unfold DelSingleNullableNTFromElemList_def DelSingleNullableNTFromElemListSet_def Language_def PartialEvalLanguage_def)
    using productionAppend3 by fastforce
  from 4 and 2 show ?thesis
    using transitiveProductions by auto
qed

lemma Del_Part14:
  assumes a: "DelNullableNTsFromElemList Rs a a'"
  shows      "a -Rs\<rightarrow>\<^sup>* a'"
proof-
  from a have 0: "\<exists>n. DelNullableNTsFromElemListInN Rs n a a'" (is "\<exists> n. ?P n")
    by(simp add: DelNullableNTsFromElemList_def)
  then obtain n where 1: "?P n" by blast
  have 2: "\<And> a a'. DelNullableNTsFromElemListInN Rs n a a' \<Longrightarrow> a -Rs\<rightarrow>\<^sup>* a'"
    apply (induction n) 
     apply (metis DelNullableNTsFromElemListInN.simps(1) ProducesInN.simps(1) Produces_def)
    using Del_Part13 by blast
  from 1 and 2 show ?thesis by blast
qed
    
lemma Del_Part15:
  assumes a: "transformDelTest G1 G2"
  assumes b: "\<And>A x. (x \<noteq> Nil \<and> A -(snd G1)\<rightarrow>\<^sup>n x \<Longrightarrow> \<exists> A'. DelNullableNTsFromElemList (snd G1) A A'  \<and> A' -(snd G2)\<rightarrow>\<^sup>* x)"
  assumes c: "ProducesInN A (snd G1) (n+1) x"
  assumes e: "x \<noteq> Nil"
  shows      "\<exists> A'. DelNullableNTsFromElemList (snd G1) A A'  \<and> A' -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from a have 0: "\<exists> S Rs1 Rs2. 
                  (S, Rs1) = G1
                  \<and> (S, Rs2) = G2
                  \<and> Rs2 = RemoveAllEpsilonProds S (DelAllNullableNTsFromRules Rs1)"
          (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformDelTest_def)
  then obtain S Rs1 Rs2 where r: "?P S Rs1 Rs2" by blast
  from r have f: "G1 = (S, Rs1)" by auto
  from r have g: "G2 = (S, Rs2)" by auto
  from r have h: "Rs2 = RemoveAllEpsilonProds S (DelAllNullableNTsFromRules Rs1)" by auto
  from c and f have 1: "\<exists> t. ProducesInN t Rs1 n x \<and> A -Rs1\<rightarrow> t"
    (is "\<exists> t. ?P t")
    by auto
  then obtain t where 2: "?P t" by blast
  from 2 have 3: "\<exists> l r N rhs. A = l @ [NT N] @ r \<and> t = l @ rhs @ r \<and> (N, rhs) \<in> Rs1"
    (is "\<exists> l r N rhs. ?P l r N rhs")
    by(unfold ProductionStep_def Productions_def, auto)
  then obtain l r N rhs where 4: "?P l r N rhs" by blast
  from 2 and b and e and g and f have 5: "\<exists> t'. DelNullableNTsFromElemList Rs1 t t'  \<and> t' -Rs2\<rightarrow>\<^sup>* x"
    (is "\<exists> t'. ?P t'")
    by auto
  then obtain t' where 6: "?P t'" by blast
  from 6 have 7: "\<exists> l' rr'. t' = l' @ rr' \<and> DelNullableNTsFromElemList Rs1 l l' \<and>  DelNullableNTsFromElemList Rs1 (rhs@r) rr'"
    (is "\<exists> l' rr'. ?P l' rr'")
    using "4" Del_Part6 by fastforce
  then obtain l' rr' where 8: "?P l' rr'" by blast
  from 8 have 9: "\<exists> r' rhs'. rr' = rhs' @ r' \<and> DelNullableNTsFromElemList Rs1 r r' \<and> DelNullableNTsFromElemList Rs1 rhs rhs'"
    (is "\<exists> r' rhs'. ?P r' rhs'")
    using Del_Part6 by fastforce
  then obtain r' rhs' where 10: "?P r' rhs'" by blast
  show ?thesis
  proof cases
    assume x: "rhs' = Nil"
    from x have 14: "t' = l' @ r'"
      by (simp add: "10" "8")
    have 16: "rhs -Rs1\<rightarrow>\<^sup>* Nil"
      using "10" Del_Part14 x by blast
    have 17: "[NT N] -Rs1\<rightarrow> rhs"
      using "4" ProductionStep_def Productions_def by fastforce
    from 17 and 16 have 18: "[NT N] -Rs1\<rightarrow>\<^sup>* Nil"
      by (meson ProducesInN.simps(2) Produces_def)
    from 18 have 17: "[] \<in> Language N Rs1"
      apply(unfold Language_def PartialEvalLanguage_def IsTerminalWord_def)
      by simp
    from 17 have 18: "DelSingleNullableNTFromElemList Rs1 [NT N] []"
      apply(unfold DelSingleNullableNTFromElemList_def DelSingleNullableNTFromElemListSet_def)
      by fastforce
    from 18 have 19: "DelNullableNTsFromElemList Rs1 [NT N] []"
      using Del_Part3 by auto
    from 19 and 8 have 20: "DelNullableNTsFromElemList Rs1 (l@[NT N]) l'"
      by (metis Del_Part11 append.right_neutral)
    from 20 and 10 have 21: "DelNullableNTsFromElemList Rs1 (l@[NT N]@r) (l'@r')"
      using Del_Part11 by fastforce
    from 21 and 14 and 4 and 6 show ?thesis 
      using f g by auto
  next
    assume y: "rhs' \<noteq> Nil"
    from 4 have 0: "[NT N] -(snd G1)\<rightarrow> rhs"
      apply(simp add: ProductionStep_def Productions_def) 
      using f by fastforce
    from 10 have 11: "DelNullableNTsFromElemList (snd G1) rhs rhs'" using f by auto
    from y and 0 and a and 11 and Del_Part7 have 12: "(N, rhs') \<in> Rs2"
      by (metis r snd_conv)
    from 8 have 15: "DelNullableNTsFromElemList (snd G1) (l@[NT N]@r) (l'@[NT N]@r)"
      by (metis Del_Part10 append.left_neutral f snd_conv)
    from 10 have 16: "DelNullableNTsFromElemList (snd G1) (l'@[NT N]@r) (l'@[NT N]@r')"
      by (metis DelNullableNTsFromElemListInN.simps(1) DelNullableNTsFromElemList_def Del_Part11 f snd_conv)
    from 15 and 16 have 17: "DelNullableNTsFromElemList (snd G1) A (l'@[NT N]@r')"
      using "4" Del_Part2 by blast
    from 12 have 18: "(l'@[NT N]@r') -Rs2\<rightarrow> t'"
      using "10" "8" CollectI ProductionStep_def Productions_def by fastforce
    from 18 and 6 have 19: "(l'@[NT N]@r') -Rs2\<rightarrow>\<^sup>* x"
      by (meson ProducesInN.simps(2) Produces_def)
    from 19 and 17 show ?thesis
      using g by auto
  qed
qed

lemma Del_Part16:
  assumes a: "transformDelTest G1 G2"
  assumes b: "x \<noteq> Nil"
  assumes c: "A -(snd G1)\<rightarrow>\<^sup>n x"
  shows      "\<exists>A'. DelNullableNTsFromElemList (snd G1) A A'  \<and> A' -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from a have 0: "\<And>A x. x \<noteq> Nil \<and> A -(snd G1)\<rightarrow>\<^sup>n x \<Longrightarrow> \<exists>A'. DelNullableNTsFromElemList (snd G1) A A'  \<and> A' -(snd G2)\<rightarrow>\<^sup>* x"
    apply (induction n) 
    apply (metis DelNullableNTsFromElemListInN.simps(1) DelNullableNTsFromElemList_def ProducesInN.simps(1) Produces_def)
    by (metis Del_Part15 Suc_eq_plus1)
  from 0 and b and c show ?thesis
    by blast
qed

lemma Del_Part17:
  assumes a: "DelSingleNullableNTFromElemList Rs [NT A] A'"
  shows      "A' = Nil"
proof-
  from a show ?thesis
    apply(simp add: DelSingleNullableNTFromElemList_def DelSingleNullableNTFromElemListSet_def)
    by (simp add: Cons_eq_append_conv)
qed

lemma Del_Part18:
  assumes a: "DelNullableNTsFromElemList Rs [NT A] A'"
  shows      "A' = Nil \<or> A' = [NT A]"
proof-
  from a have 0: "\<exists>n. DelNullableNTsFromElemListInN  Rs n [NT A] A'" (is "\<exists> n. ?P n")
    by (simp add: DelNullableNTsFromElemList_def)  
  then obtain n where 1: "?P n" by blast
  show ?thesis
  proof cases
    assume x: "n = 0"
    from x and 1 show ?thesis
      by simp
  next
    assume y: "n \<noteq> 0"
    from y have x: "n > 0" by auto
    from x and 1 have 2: "\<exists> t. DelSingleNullableNTFromElemList Rs [NT A] t \<and> DelNullableNTsFromElemListInN  Rs (n-1) t A'"
    (is "\<exists> t. ?P t")
      by (metis DelNullableNTsFromElemListInN.elims(2) diff_Suc_1 not_gr_zero) 
    then obtain t where 3: "?P t" by blast
    from 3 have 4: "t = Nil" 
      by (meson Del_Part17)
    from 4 and 3 have 5: "A' = Nil"
      using DelNullableNTsFromElemList_def Del_Part12 by blast
    from 5 show ?thesis by auto
  qed
qed


lemma Del_Part19:
  assumes a: "Produces [] Rs a"
  shows      "a = []"
proof-
  have 0: "\<And> a. \<not> ProductionStep [] Rs a"
    apply(unfold ProductionStep_def Productions_def)
    by auto
  from a have 1: "\<exists> n. ProducesInN [] Rs n a"(is "\<exists> n. ?P n")
    by (simp add: Produces_def)
  then obtain n where 2: "?P n" by blast  
  from 2 and 0 show ?thesis
    by(induction n, auto)
qed

lemma Del_Part20:
  assumes a: "transformDelTest G1 G2"
  assumes c: "Produces [NT A] (snd G1) x"
  assumes d: "x \<noteq> Nil"
  shows      "[NT A] -(snd G2)\<rightarrow>\<^sup>* x"
proof-
  from a have 0: "\<exists> S Rs1 Rs2. 
                  (S, Rs1) = G1
                  \<and> (S, Rs2) = G2
                  \<and> Rs2 = RemoveAllEpsilonProds S (DelAllNullableNTsFromRules Rs1)"
          (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformDelTest_def)
  then obtain S Rs1 Rs2 where r: "?P S Rs1 Rs2" by blast
  from r have e: "G1 = (S, Rs1)" by auto
  from r have f: "G2 = (S, Rs2)" by auto
  from r have g: "Rs2 = RemoveAllEpsilonProds S (DelAllNullableNTsFromRules Rs1)" by auto
  from c have 1: "\<exists> n. ProducesInN [NT A] (snd G1) n x"  (is "\<exists> n. ?P n")
    by (simp add: Produces_def)
  then obtain n where 2: "?P n" by blast
  from 2 and d and a have 3:  "\<exists>A'. DelNullableNTsFromElemList (snd G1) [NT A] A'  \<and> A' -(snd G2)\<rightarrow>\<^sup>* x"
    (is "\<exists> A'. ?P A'")
    using Del_Part16 by blast
  then obtain A' where 4: "?P A'" by blast
  from 4 have 5: "A' = Nil \<or> A' = [NT A]" 
    by (meson Del_Part18)
  from 4 and d have 6: "A' \<noteq> Nil" 
    using Del_Part19 by blast
  from 5 and 6 and 4 show ?thesis 
    by blast
qed

lemma Del_Part21:
  assumes a: "[NT N] -Rs\<rightarrow> []"
  shows      "(N, []) \<in> DelAllNullableNTsFromRules Rs"
proof-
  from a have 0: "[NT N] -Rs\<rightarrow>\<^sup>* []"
    by (meson ProducesInN.simps(1) ProducesInN.simps(2) Produces_def)
  from a have 1: "DelSingleNullableNTFromElemList Rs [NT N] []"
    apply(unfold DelSingleNullableNTFromElemList_def DelSingleNullableNTFromElemListSet_def Language_def PartialEvalLanguage_def) 
    using "0" IsTerminalWord_def by fastforce
  from 1 have 2: "DelNullableNTsFromElemList Rs [NT N] []"
    by (simp add: Del_Part3)
  from 2 show ?thesis
    apply(unfold DelAllNullableNTsFromRules_def DelNullableNTsFromRule_def)
    by (smt (verit, ccfv_SIG) Del_Part6 Elem.inject(1) Nil_is_append_conv Pair_inject 
        ProductionStep_def Productions_def append.left_neutral append_self_conv assms list.inject mem_Collect_eq)
qed

lemma Del_Part23:
  assumes a: "[NT N] -Rs\<rightarrow> (NT A) # t"
  assumes b: "[NT A] -Rs\<rightarrow>\<^sup>* []"
  shows      "(N, t) \<in> DelAllNullableNTsFromRules Rs"
proof-
  from a have 0: "(N, (NT A)#t) \<in> Rs"
    by (smt (verit, ccfv_threshold) Elem.inject(1) Nil_is_append_conv Pair_inject ProductionStep_def
        Productions_def append.right_neutral append_eq_Cons_conv append_self_conv2 list.inject mem_Collect_eq not_Cons_self2)
  from b have 1: "DelSingleNullableNTFromElemList Rs ((NT A) # t) t"
    apply(unfold DelSingleNullableNTFromElemList_def DelSingleNullableNTFromElemListSet_def Language_def PartialEvalLanguage_def)
    using IsTerminalWord_def by force
  from 1 have 2: "DelNullableNTsFromElemList Rs ((NT A) # t) t"
    by (simp add: Del_Part3)
  from 2 and 0 show ?thesis
    apply (unfold DelAllNullableNTsFromRules_def DelNullableNTsFromRule_def)
    by auto
qed


lemma Del_Part24:
  assumes a: "[a] -Rs\<rightarrow>\<^sup>* []"
  shows      "\<exists> b. a = (NT b)"
proof-
  have 0: "\<And> a b. \<not> ([T a] -Rs\<rightarrow> b)"
    apply (simp add: ProductionStep_def Productions_def) 
    by (simp add: Cons_eq_append_conv)
  from a have 1: "\<exists> n. [a] -Rs\<rightarrow>\<^sup>n []" (is "\<exists> n. ?P n")
    by (simp add: Produces_def)
  then obtain n where 2: "?P n" by blast
  from 2 have 3: "n > 0" 
    using ProducesInN.simps(1) bot_nat_0.not_eq_extremum by blast
  from 3 have 4: "\<exists> t. [a] -Rs\<rightarrow> t" 
    by (meson "2" ProducesInN.elims(2) list.discI)
  from 4 and 0 have 5: "\<not> (\<exists> b. a = (T b))"
    by blast
  from 5 show ?thesis 
    by (meson Elem.exhaust)
qed

lemma Del_Part25:
  assumes a: "[a] -Rs\<rightarrow>\<^sup>* []"
  shows      "DelNullableNTsFromElemList Rs (a # t) t"
proof-
  from a have 0: "\<exists> b. a = (NT b)" (is "\<exists> b. ?P b")
    using Del_Part24 by blast
  then obtain b where 1: "?P b" by blast
  from 1 and a have 2: "DelSingleNullableNTFromElemList Rs (a # t) t"
    apply(unfold DelSingleNullableNTFromElemList_def DelSingleNullableNTFromElemListSet_def Language_def PartialEvalLanguage_def IsTerminalWord_def)
    by fastforce
  from 2 show ?thesis
    by (simp add: Del_Part3)
qed

lemma Del_Part26:
  assumes a: "t -Rs\<rightarrow>\<^sup>* []"
  shows      "DelNullableNTsFromElemList Rs t []"
proof-
  have 0: "\<And> a t.  a # t -Rs\<rightarrow>\<^sup>* [] \<Longrightarrow> [a] -Rs\<rightarrow>\<^sup>* [] \<and> t -Rs\<rightarrow>\<^sup>* []"
    by (metis (no_types, opaque_lifting) Nil_is_append_conv append.left_neutral append_Cons productionParts3)
  from a show ?thesis
    apply (induction t) 
    apply (meson DelNullableNTsFromElemListInN.simps(1) DelNullableNTsFromElemList_def) 
    using "0" Del_Part2 Del_Part25 by blast
qed

lemma Del_Part27:
  assumes a: "[] \<in> Language N Rs"
  shows      "(N, []) \<in> DelAllNullableNTsFromRules Rs"
proof-
  from a have 0: "[NT N] -Rs\<rightarrow>\<^sup>* []"
    by (simp add: Language_def PartialEvalLanguage_def)
  from 0 have 1: "\<exists> n. ProducesInN [NT N] Rs n []" (is "\<exists> n. ?P n")
    by (simp add: Produces_def)
  then obtain n where 2: "?P n" by blast
  from 2 have 3: "n > 0" 
    using ProducesInN.simps(1) bot_nat_0.not_eq_extremum by blast
  from 3 and 2 have 4: "\<exists> t. ProductionStep [NT N] Rs t \<and> Produces t Rs []" (is "\<exists> t. ?P t")
    by (meson ProducesInN.elims(2) Produces_def list.discI)
  then obtain t where 5: "?P t" by blast
  from 5 have 6: "Produces t Rs []" by auto
  from 5 have 7: "ProductionStep [NT N] Rs t" by auto
  from 7 have 8: "(N, t) \<in> Rs" 
    by (smt (verit, ccfv_threshold) CollectD Elem.inject(1) Pair_inject ProductionStep_def 
        Productions_def append_eq_Cons_conv append_is_Nil_conv append_self_conv list.inject self_append_conv2)
  from 6 and 7 show ?thesis
    apply (unfold DelAllNullableNTsFromRules_def DelNullableNTsFromRule_def, auto)
    apply (rule_tac x="t" in exI) 
    using "8" Del_Part26 by blast
qed

lemma Del_Part28:
  assumes a: "transformDelTest G1 G2"
  assumes b: "x \<in> \<lbrakk>G1\<rbrakk>"
  shows      "x \<in> \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0: "\<exists> S Rs1 Rs2. 
                (S, Rs1) = G1
                \<and> (S, Rs2) = G2
                \<and> Rs2 = RemoveAllEpsilonProds S (DelAllNullableNTsFromRules Rs1)"
        (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformDelTest_def)
  then obtain S Rs1 Rs2 where r: "?P S Rs1 Rs2" by blast
  show ?thesis
  proof cases
    assume x: "x = Nil"
    from b and x and r have 1: "[] \<in> Language S Rs1"
      using Lang_def fst_conv snd_conv by fastforce
    from 1 have 2: "(S, []) \<in> DelAllNullableNTsFromRules Rs1"
      by (simp add: Del_Part27)
    from 2 have 3: "(S, []) \<in> RemoveAllEpsilonProds S (DelAllNullableNTsFromRules Rs1)"
      apply (unfold RemoveAllEpsilonProds_def) 
      by blast
    from 3 have 4: "[NT S] -Rs2\<rightarrow> []"
      by (simp add: ProductionStep_def Productions_def r)
    from 4 have 5: "[NT S] -Rs2\<rightarrow>\<^sup>* []"
      by (meson ProducesInN.simps(1) ProducesInN.simps(2) Produces_def)
    from 5 and x show ?thesis
      apply (unfold Lang_def Language_def PartialEvalLanguage_def IsTerminalWord_def, auto)
      using r by blast
  next
    assume x: "x \<noteq> Nil"
    from b have 1: "Produces [NT S] Rs1 x" 
      apply(unfold Lang_def Language_def PartialEvalLanguage_def IsTerminalWord_def, auto)
      using r by blast
    from 1 and x and a have 2: "[NT S] -Rs2\<rightarrow>\<^sup>* x"
      by (metis Del_Part20 r snd_conv)
    from 2 show ?thesis
      using IsTerminalWord_def Lang_def Language_def PartialEvalLanguage_def b r by fastforce
  qed
qed

lemma Del_Part29:
  assumes a: "Rs2 = RemoveAllEpsilonProds S (DelAllNullableNTsFromRules Rs1)"
  assumes b: "(\<And>A x. A -Rs2\<rightarrow>\<^sup>n x \<Longrightarrow> A -Rs1\<rightarrow>\<^sup>* x)" 
  assumes c: "ProducesInN A Rs2 (Suc n) x" 
  shows      "A -Rs1\<rightarrow>\<^sup>* x"
proof-  
  from c have 0: "\<exists> t. A -Rs2\<rightarrow> t \<and> t -Rs2\<rightarrow>\<^sup>n x" (is "\<exists> t. ?P t")
    by simp
  then obtain t where 1: "?P t" by blast
  from 1 have 2: "\<exists> l r N rhs. A = l @ [NT N] @ r \<and> t = l @ rhs @ r \<and> (N, rhs) \<in> Rs2" 
  (is "\<exists> l r N rhs. ?P l r N rhs")
    apply (unfold ProductionStep_def Productions_def) 
    by blast
  then obtain l r N rhs where 3: "?P l r N rhs" by blast
  from 3 and a have 4: "(N, rhs) \<in> DelAllNullableNTsFromRules Rs1"
    apply (unfold RemoveAllEpsilonProds_def)
    by blast
  from 4 have 5: "\<exists> rhs'. (N, rhs') \<in> Rs1 \<and> DelNullableNTsFromElemList Rs1 rhs' rhs"
    (is "\<exists> rhs'. ?P rhs'")
    by (unfold DelAllNullableNTsFromRules_def DelNullableNTsFromRule_def, auto)
  then obtain rhs' where 6: "?P rhs'" by blast
  from 6 have 7: "rhs' -Rs1\<rightarrow>\<^sup>* rhs" 
    by (simp add: Del_Part14)
  from 6 have 8: "[NT N] -Rs1\<rightarrow> rhs'"
    using ProductionStep_def Productions_def by fastforce
  from 8 and 7 have 9: "[NT N] -Rs1\<rightarrow>\<^sup>* rhs"
    by (meson ProducesInN.simps(2) Produces_def)
  from 9 and 3 have 10: "A -Rs1\<rightarrow>\<^sup>* t" 
    using productionAppend3 by blast
  from 1 and b have 11: "t -Rs1\<rightarrow>\<^sup>* x"
    by blast
  from 10 and 11 show ?thesis
    using transitiveProductions by auto
qed
    
lemma Del_Part30:
  assumes a: "transformDelTest G1 G2"
  assumes b: "A -(snd G2)\<rightarrow>\<^sup>n x"
  shows      "A -(snd G1)\<rightarrow>\<^sup>* x"
proof-
  from a have 0: "\<exists> S Rs1 Rs2. 
                (S, Rs1) = G1
                \<and> (S, Rs2) = G2
                \<and> Rs2 = RemoveAllEpsilonProds S (DelAllNullableNTsFromRules Rs1)"
        (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformDelTest_def)
  then obtain S Rs1 Rs2 where 1: "?P S Rs1 Rs2" by blast
  from b and 1 have 2: "A -Rs2\<rightarrow>\<^sup>n x" by auto
  have 3: "\<And> A x. A -Rs2\<rightarrow>\<^sup>n x \<Longrightarrow> A -Rs1\<rightarrow>\<^sup>* x"
    apply (induction n) 
    apply (metis ProducesInN.simps(1) Produces_def)
    by (metis "1" Del_Part29)
  from 2 and 3 show ?thesis
    using "1" by fastforce
qed    


lemma Del_Part31:
  assumes a: "transformDelTest G1 G2"
  assumes b: "x \<in> \<lbrakk>G2\<rbrakk>"
  shows      "x \<in> \<lbrakk>G1\<rbrakk>"
proof-
  from b have 0: "[(NT (fst G2))] -(snd G2)\<rightarrow>\<^sup>* x"
    by (unfold Lang_def Language_def PartialEvalLanguage_def, auto)
  from 0 have 1: "\<exists> n. [(NT (fst G2))] -(snd G2)\<rightarrow>\<^sup>n x" (is "\<exists> n. ?P n")
    by (simp add: Produces_def)
  then obtain n where 2: "?P n" by blast
  from 2 have 3: "[(NT (fst G2))] -(snd G1)\<rightarrow>\<^sup>* x"
    using Del_Part30 a by blast
  from a have 4: "fst G1 = fst G2" 
    by (unfold transformDelTest_def, auto)
  from b have 5: "IsTerminalWord x" 
    by (unfold Lang_def Language_def PartialEvalLanguage_def, auto)
  from 4 and 3 and 5 show ?thesis
    apply (unfold Lang_def Language_def PartialEvalLanguage_def, auto)
    by (metis prod.collapse)
qed

theorem verifyTransformDel: 
  assumes a: "transformDelTest G1 G2"
  shows      "\<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
proof-
  from a have 0: "\<And>x. x \<in> \<lbrakk>G1\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G2\<rbrakk>"
    by (simp add: Del_Part28)
  from a have 1: "\<And>x. x \<in> \<lbrakk>G2\<rbrakk> \<Longrightarrow> x \<in> \<lbrakk>G1\<rbrakk>"
    by (simp add: Del_Part31)
  from 0 and 1 show ?thesis
    by blast
qed

definition finiteCFG :: "('n, 't) CFG \<Rightarrow> bool"
  where "finiteCFG G \<equiv> finite (snd G)"

lemma StartFinite:
  assumes a: "transformStartTest G1 S0 G2"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG G2"
proof-
  from a and b show ?thesis
    by (metis finiteCFG_def finite_insert snd_conv transformStartTest_def)
qed

lemma TermFinite:
  assumes a: "transformTermTest G1 N G2"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG G2"
proof-
  from a and b show ?thesis
    by (unfold transformTermTest_def finiteCFG_def, auto)
qed

lemma BinFinite:
  assumes a: "transformBinTest G1 N G2"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG G2"
proof-
  from a and b show ?thesis
    by (unfold transformBinTest_def finiteCFG_def, auto)
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
  shows      "finite (NewUnitTransRuleSet N Rs1)"
proof-
  from a and UnitFinit_part3 have 0: "finite (NTToNTProductionSet Rs1)"
    by (auto)
  from 0 and a and UnitFinit_part4 have 1: "finite {(A, Rhs). \<exists>B. (B, Rhs) \<in> Rs1 \<and> (A, B) \<in> (NTToNTProductionSet Rs1)}"
    by (smt (verit, del_insts) Collect_cong Pair_inject case_prodE case_prodI2)
  have 2: "NewUnitTransRuleSet N Rs1 \<subseteq> {(A, Rhs). \<exists>B. (B, Rhs) \<in> Rs1 \<and> (A, B) \<in> (NTToNTProductionSet Rs1)}"
    by (smt (verit, best) NewUnitTransRuleSet_def Pair_inject case_prodI2 mem_Collect_eq subsetI)
  from 1 and 2 show ?thesis
    using finite_subset by blast
qed
  
lemma UnitFinite:
  assumes a: "transformUnitTest G1 N G2"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG G2"
proof-
  from a and b and UnitFinit_part5 show ?thesis
    by (metis finiteCFG_def finite_Diff finite_UnI snd_conv transformUnitTest_def)
qed

lemma listFinite:
  fixes      L :: "'a list"
  shows      "finite (set L)"
  by auto

definition RuleElementListSubset :: "('n, 't) Elem list \<Rightarrow> ('n, 't) Elem list \<Rightarrow> bool"
  where "RuleElementListSubset E1 E2 \<equiv> set E1 \<subseteq> set E2" 

definition RuleElementListSize :: "('n, 't) Elem list \<Rightarrow> ('n, 't) Elem list \<Rightarrow> bool"
  where "RuleElementListSize E1 E2 \<equiv> size E1 \<le> size E2" 

lemma DelFinite_Part1:
  assumes a: "(E1, E2) \<in> DelSingleNullableNTFromElemListSet Rs"
  shows      "RuleElementListSubset E1 E2"
proof-
  from a show ?thesis
    apply (simp add: DelSingleNullableNTFromElemListSet_def RuleElementListSubset_def)
    by force
qed

lemma DelFinite_Part2:
  assumes a: "DelSingleNullableNTFromElemList Rs E1 E2"
  shows      "RuleElementListSubset E2 E1"
proof-
  from a and DelFinite_Part1 show ?thesis
    by (simp add: DelSingleNullableNTFromElemList_def, auto)
qed

lemma DelFinite_Part3:
  assumes a: "DelNullableNTsFromElemList Rs E1 E2"
  shows      "RuleElementListSubset E2 E1"
proof-
  from a have 0: "\<exists> n. DelNullableNTsFromElemListInN Rs n E1 E2" (is "\<exists> n. ?P n")
    by (simp add: DelNullableNTsFromElemList_def)
  then obtain n where 1: "?P n" by blast
  have 2: "\<And> E1 E2. DelNullableNTsFromElemListInN Rs n E1 E2 \<Longrightarrow> RuleElementListSubset E2 E1"
    apply (induction n, auto) 
    using RuleElementListSubset_def apply auto[1]
    using DelFinite_Part2 
    by (metis RuleElementListSubset_def order_trans)
  from 2 and 1 show ?thesis
    by auto
qed

lemma DelFinite_Part4:
  assumes a: "(E1, E2) \<in> DelSingleNullableNTFromElemListSet Rs"
  shows      "RuleElementListSize E1 E2"
proof-
  from a show ?thesis
    apply (simp add: DelSingleNullableNTFromElemListSet_def RuleElementListSize_def)
    by force
qed

lemma DelFinite_Part5:
  assumes a: "DelSingleNullableNTFromElemList Rs E1 E2"
  shows      "RuleElementListSize E2 E1"
proof-
  from a and DelFinite_Part4 show ?thesis
    by (simp add: DelSingleNullableNTFromElemList_def, auto)
qed

lemma DelFinite_Part6:
  assumes a: "DelNullableNTsFromElemList Rs E1 E2"
  shows      "RuleElementListSize E2 E1"
proof-
  from a have 0: "\<exists> n. DelNullableNTsFromElemListInN Rs n E1 E2" (is "\<exists> n. ?P n")
    by (simp add: DelNullableNTsFromElemList_def)
  then obtain n where 1: "?P n" by blast
  have 2: "\<And> E1 E2. DelNullableNTsFromElemListInN Rs n E1 E2 \<Longrightarrow> RuleElementListSize E2 E1"
    apply (induction n, auto) 
    using RuleElementListSize_def apply auto[1]
    using DelFinite_Part5
    by (metis RuleElementListSize_def order_trans)
  from 2 and 1 show ?thesis
    by auto
qed

lemma DelFinite_Part7:
  fixes      S :: "'a set"
  fixes      H :: "'a list set"
  fixes      n :: "nat"
  assumes a: "finite S"
  assumes b: "H = {L | L. (set L) \<subseteq> S \<and> (size L) \<le> n}"
  shows      "finite H"
  using a and b apply-
  apply (induction n)
  apply auto[1]
  using finite_lists_length_le by force

lemma DelFinite_Part8: 
  assumes a: "H = {E2. DelNullableNTsFromElemList Rs E1 E2}"
  shows      "finite H"
proof-
  from a have 0: "H \<subseteq> {E. RuleElementListSize E E1 \<and> RuleElementListSubset E E1}"
    by (simp add: Collect_mono_iff DelFinite_Part3 DelFinite_Part6)
  from 0 have 1: "H \<subseteq> {E. size E \<le> size E1 \<and> set E \<subseteq> set E1}"
    by (simp add: RuleElementListSize_def RuleElementListSubset_def)
  have 2: "finite (set E1)"
    by auto
  from 2 and 1 and DelFinite_Part7 show ?thesis
    by (metis (no_types, lifting) mem_Collect_eq rev_finite_subset subsetI)
qed

definition DelAllNullableNTsFromRule :: "('n, 't) RuleSet \<Rightarrow> ('n, 't) Rule \<Rightarrow> ('n, 't) RuleSet"
  where "DelAllNullableNTsFromRule X R = { NR | NR. DelNullableNTsFromRule X R NR}"

lemma DelFinite_Part9: 
  assumes a: "finite Rs"
  shows      "finite (DelAllNullableNTsFromRule Rs R)"
proof-
  have 0: "\<And> S. S \<in> DelAllNullableNTsFromRule Rs R \<Longrightarrow> (snd S) \<in> {E2. DelNullableNTsFromElemList Rs (snd R) E2}"
    apply (unfold DelAllNullableNTsFromRule_def DelNullableNTsFromRule_def)
    by fastforce
  have 1: "\<And> S. S \<in> DelAllNullableNTsFromRule Rs R \<Longrightarrow> (fst S) = (fst R)"
    apply (unfold DelAllNullableNTsFromRule_def DelNullableNTsFromRule_def)
    by fastforce
  from 0 and 1 have 2: " DelAllNullableNTsFromRule Rs R \<subseteq> CartesianProduct {fst R} {E2. DelNullableNTsFromElemList Rs (snd R) E2}"
    by (unfold CartesianProduct_def, auto)
  have 3: "finite {E2. DelNullableNTsFromElemList Rs (snd R) E2}"
    by (simp add: DelFinite_Part8)
  from 2 and 3 show ?thesis
    by (meson CartesianFinite finite.emptyI finite.insertI finite_subset)
qed
    
lemma DelFinite_Part10: 
  assumes a: "finite Rs"
  shows      "finite (DelAllNullableNTsFromRules Rs)"
proof-
  have 0: "DelAllNullableNTsFromRules Rs \<subseteq> \<Union> {DelAllNullableNTsFromRule Rs R | R. R \<in> Rs}"
    apply (simp add: DelAllNullableNTsFromRules_def DelAllNullableNTsFromRule_def)
    by blast
  have 1: "finite (\<Union> {DelAllNullableNTsFromRule Rs R | R. R \<in> Rs})"
    using a and DelFinite_Part9  
    by (metis Collect_mem_eq finite_UN_I setcompr_eq_image)
  from 0 and 1 show ?thesis
    using finite_subset by blast
qed

lemma DelFinite:
  assumes a: "transformDelTest G1 G2"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG G2"
proof-
  have 0: "\<And> R S. RemoveAllEpsilonProds S R \<subseteq> R"
    by(unfold RemoveAllEpsilonProds_def, auto)
  from a and b and 0 show ?thesis
    using DelFinite_Part10 apply (unfold transformDelTest_def finiteCFG_def)
    using finite_subset by fastforce
qed

(* Measure for Term to prove that it terminates *)

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

lemma foldRemove:
  fixes      f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes      E :: "'a"
  fixes      Z :: "'b"
  assumes a: "comp_fun_commute_on S f"
  assumes b: "finite S"
  assumes c: "E \<in> S"
  shows      "Finite_Set.fold f Z S = f E (Finite_Set.fold f Z (S- {E}))"
proof-
  have 0: "E \<notin> S - {E}"
    by auto
  from c have 1: "S = insert E (S - {E})"
    by auto
  from 0 and 1 and a and b show ?thesis
    using foldInsert 
    by (metis finite_Diff)
qed

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


lemma TermTerminate_Part1:
  assumes x: "transformTermTest G1 N G2"
  assumes y: "finiteCFG G1"
  shows      "TermMeasure G1 > TermMeasure G2"
proof-
  from x have 1: "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
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
    by (simp add: transformTermTest_def)
  from 1 obtain S R1 R2 R3 Rs1 Rs2 S1 L R a where r: "?P S R1 R2 R3 Rs1 Rs2 S1 L R a" by blast
  from r have a: "R1 = (S1, L @ T a # R)" by auto
  from r have b: "R2 = (S1, L @ NT N # R)" by auto
  from r have c: "R3 = (N, [T a])" by auto
  from r have d: "(L @ R \<noteq> [])" by auto
  from r have e: "G1 = (S, Rs1)" by auto
  from r have f: "G2 = (S, Rs2)" by auto
  from r have i: "R1 \<in> Rs1" by auto
  from r have j: "Rs2 = {R2, R3} \<union> (Rs1 - {R1})" by auto
  from r have k: "NT N \<notin> NonTerminals G1" by auto
  from c have 2: "CountNonSingleTerminals R3 = 0" by simp
  from a and b and d have 3: "CountNonSingleTerminals R1 = CountNonSingleTerminals R2 + 1"
    by (meson CountProperty2)
  from y and e have 0: "finite Rs1" by (simp add: finiteCFG_def)
  have 4: "\<And> Rs. comp_fun_commute_on Rs TermFold "
    apply (unfold comp_fun_commute_on_def TermFold_def) 
    by fastforce
  from 4 and i and 0 have 5: "TermFold R1 (TermRuleMeasure (Rs1 - {R1})) = TermRuleMeasure Rs1"
    apply (unfold TermRuleMeasure_def)
    by (simp add: "4" foldRemove)
  from 5 have 6: "CountNonSingleTerminals R1 + (TermRuleMeasure (Rs1 - {R1})) = TermRuleMeasure Rs1"
    by (unfold TermFold_def, auto)
  from b and k have 7: "R2 \<notin> Rs1"
    apply (unfold NonTerminals_def NTInRule_def)
    using e by fastforce
  from c and k have 8: "R3 \<notin> Rs1"
    apply (unfold NonTerminals_def NTInRule_def)
    using e  by auto
  from 7 have 9: "R2 \<notin> (Rs1 - {R1})"
    by auto
  from 9 and 0 and 4 have 10: "TermFold R2 (TermRuleMeasure (Rs1 - {R1})) = TermRuleMeasure ({R2} \<union> (Rs1 - {R1}))"
    by (metis TermRuleMeasure_def finite_Diff  foldInsert insert_is_Un)
  from 10 have 11: "CountNonSingleTerminals R2 + (TermRuleMeasure (Rs1 - {R1})) = TermRuleMeasure ({R2} \<union> (Rs1 - {R1}))"
    by (simp add: TermFold_def)
  from 8 have 12: "R3 \<notin> {R2} \<union> (Rs1 - {R1})"
    by (smt (verit, best) Un_iff add_is_1 append_self_conv2 empty_iff insert_Diff
        insert_iff length_0_conv length_Cons length_append list.inject r snd_conv)  
  from 12 and 4 have 13: "TermFold R3 (TermRuleMeasure ({R2} \<union> (Rs1 - {R1}))) = TermRuleMeasure ({R2, R3} \<union> (Rs1 - {R1}))"
    by (smt (verit) "0" TermRuleMeasure_def Un_insert_left finite_Diff finite_insert foldInsert insert_commute sup_bot_left)
  from 13 and 12 have 14: "CountNonSingleTerminals R3 + CountNonSingleTerminals R2 + (TermRuleMeasure (Rs1 - {R1})) = TermRuleMeasure (Rs2)"
    by (simp add: "11" "2" TermFold_def j)
  from 14 and 6 and 2 and 3 show ?thesis
    by (metis Suc_eq_plus1 TermMeasure_def add_Suc add_cancel_left_left e f less_add_same_cancel2 less_numeral_extra(1) snd_eqD)
qed

lemma TermTerminate_Part2:
  assumes a: "\<And> R. R \<in> Rs \<Longrightarrow> CountNonSingleTerminals R = 0"
  assumes b: "finite Rs"
  shows      "fold_graph TermFold 0 Rs 0"
proof-
  have 0: "\<And> Rs. comp_fun_commute_on Rs TermFold "
    apply (unfold comp_fun_commute_on_def TermFold_def) 
    by fastforce
  from 0 have 1: "comp_fun_commute_on Rs TermFold" by auto
  have 2: "finite Rs \<Longrightarrow> (\<And> R. R \<in> Rs \<Longrightarrow> CountNonSingleTerminals R = 0) \<Longrightarrow> fold_graph TermFold 0 Rs 0"
    apply (induct rule: finite_induct) 
    using fold_graph.emptyI apply fastforce
    by (metis TermFold_def add.right_neutral fold_graph.insertI insertCI)
  from 2 show ?thesis
    using a b by blast
qed

lemma TermTerminate_Part3:
  assumes a: "\<And> R. R \<in> Rs \<Longrightarrow> CountNonSingleTerminals R = 0"
  assumes b: "finite Rs"
  shows      "TermRuleMeasure Rs = 0"
proof-
  from a and b have 0: "fold_graph TermFold 0 Rs 0"
    using TermTerminate_Part2 by blast
  from b and 0 have 1: "\<And> x. fold_graph TermFold 0 Rs x \<Longrightarrow> x = 0"
    by (smt (verit) TermFold_def a empty_iff fold_graph_closed_lemma insert_iff plus_nat.add_0)
  from b and 1 show ?thesis
    apply (unfold TermRuleMeasure_def Finite_Set.fold_def, auto)
    using "0" by blast
qed

lemma TermTerminate_Part4:
  assumes a: "\<And> t . (T t) \<notin> set E"
  shows      "CountTerminals E = 0"
proof-
  from a show ?thesis
    apply (induction E)
     apply (auto)
    by (metis CountTerminals.simps(3) Elem.exhaust)
qed

lemma TermTerminate_Part5:
  assumes a: "CountNonSingleTerminals R > 0"
  shows      "\<exists> l r t. snd R = l @ [T t] @ r \<and> l @ r \<noteq> []"
proof-
  from a have 0: "CountTerminals (snd R) > 0"
    by (metis CountNonSingleTerminals.elims gr0I snd_conv)
  from 0 have 1: "\<exists> t. (T t) \<in> set (snd R)"
    using TermTerminate_Part4 by fastforce
  from 1 have 2: "\<exists> l r t. snd R = l @ [T t] @ r " (is "\<exists> l r t. ?P l r t")
    by (metis append.left_neutral append_Cons in_set_conv_decomp)
  then obtain l r t where 3: "?P l r t" by blast
  have 4: "CountNonSingleTerminals (fst R, [T t]) = 0"
    by simp
  from 3 and 4 and a have 5: "l @ r \<noteq> []"
    by (metis append.right_neutral append_is_Nil_conv append_self_conv2 less_nat_zero_code prod.collapse)
  from 5 and 3 show ?thesis
    by auto
qed

lemma TermTerminate_Part6:
  assumes a: "TermMeasure G1 > 0"
  assumes b: "(NT N) \<notin> NonTerminals G1"
  shows      "\<exists> G2. transformTermTest G1 N G2"
proof-
  from a have 0: "\<exists> R. R \<in> snd G1 \<and> CountNonSingleTerminals R > 0" (is "\<exists> R. ?P R")
    apply (unfold TermMeasure_def) 
    by (metis Finite_Set.fold_def TermRuleMeasure_def 
        TermTerminate_Part3 bot_nat_0.not_eq_extremum) 
  then obtain R where 1: "?P R" by blast
  from 1 have 2: "\<exists> l r t S1 rhs. rhs = l @ [T t] @ r \<and> l @ r \<noteq> [] \<and> (S1, rhs) = R" 
    (is "\<exists> l r t S1 rhs. ?P l r t S1 rhs")
    by (metis TermTerminate_Part5 old.prod.exhaust snd_conv)
  then obtain l r t S1 rhs where 3: "?P l r t S1 rhs" by blast
  have 4: "\<exists> Rs1 S. (S, Rs1) = G1" (is "\<exists> Rs1 S. ?P Rs1 S")
    using prod.collapse by blast
  then obtain Rs1 S where 5: "?P Rs1 S" by blast
  from 5 and 3 and b show ?thesis
    apply (unfold transformTermTest_def, rule_tac x="(S, ({(S1, l @ [NT N] @ r), (N, [T t])} \<union> (Rs1-{R})))" in exI,
          rule_tac x="S" in exI, simp, rule_tac x="S1" in exI, simp, rule_tac x="rhs" in exI, simp, rule_tac x="l @ [NT N] @ r" in exI, simp, 
          rule_tac x="N" in exI, simp, rule_tac x="[T t]" in exI, simp, rule_tac x="Rs1" in exI, simp, rule_tac x="l" in exI, simp) 
    using "1" by force
qed


type_synonym ('n, 't) NTGen = "('n, 't) CFG \<Rightarrow> 'n"

definition NewNTGen :: "('n, 't) NTGen \<Rightarrow> bool"
  where "NewNTGen Gen \<equiv> (\<forall> Cfg. (NT (Gen Cfg)) \<notin> NonTerminals Cfg)"

function (domintros) transformTerm :: "('n, 't) NTGen \<Rightarrow> ('n, 't) CFG \<Rightarrow> ('n, 't) CFG"
  where "transformTerm Gen G1 = (if (TermMeasure G1 = 0) then G1 else 
                                (transformTerm Gen (SOME G2. transformTermTest G1 (Gen G1) G2)))"
  by pat_completeness auto

lemma TermTerminate_Part7:
  assumes a: "finiteCFG G"
  shows      "\<forall> G2. (transformTermTest G (Gen G) G2 \<longrightarrow> finiteCFG G2 \<and> TermMeasure G2 < TermMeasure G)"
proof-
  from a show ?thesis 
    by (simp add: TermFinite TermTerminate_Part1)
qed


lemma TermTerminate_Part8:
  assumes a: "TermMeasure G > 0"
  assumes b: "NewNTGen Gen"
  shows      "\<exists> G2. (transformTermTest G (Gen G) G2)"
proof-
  from b have 0: "(NT (Gen G)) \<notin> NonTerminals G"
    using NewNTGen_def by blast
  from 0 and a show ?thesis
    by (meson TermTerminate_Part6)
qed

lemma TermTerminate_Part9:
  assumes d: "NewNTGen Gen"
  assumes a: "\<And> G. (TermMeasure G < n \<and> finiteCFG G) \<Longrightarrow> transformTerm_dom (Gen, G)"
  assumes b: "TermMeasure G = n"
  assumes c: "finiteCFG G"
  shows      "transformTerm_dom (Gen, G)"
proof-
  show ?thesis
  proof cases
    assume x: "n = 0"
    have 0: "\<And> G gen. TermMeasure G = 0 \<Longrightarrow> transformTerm_dom (gen, G)"
      apply (rule transformTerm.domintros)
      by fastforce
    from x and 0 and b show ?thesis by blast
  next
    assume y: "n \<noteq> 0"
    from y have x: "n > 0" by auto
    from b and x have 0: "TermMeasure G > 0" by auto
    have 1: "\<And> G2. transformTermTest G (Gen G) G2 \<Longrightarrow> TermMeasure G2 < n  \<and> finiteCFG G2"
      using TermTerminate_Part7 and TermTerminate_Part8 
      using b c d by blast
    have 2: "\<exists> G2. transformTermTest G (Gen G) G2"
      using TermTerminate_Part7 and TermTerminate_Part8 
      using "0" d by blast
    from a and 1 and d have 3: "\<And> G2. transformTermTest G (Gen G) G2 \<Longrightarrow> transformTerm_dom (Gen, G2)"
      by blast
    from 3 and 2 have 4: "transformTerm_dom (Gen, (SOME G2. transformTermTest G (Gen G) G2))"
      by (simp add: someI_ex)
    from 0 and 4 show ?thesis
      by (meson transformTerm.domintros)
  qed
qed

lemma TermTerminate_Part10:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  shows      "transformTerm_dom (Gen, G1)"
proof-
  have 0: "\<exists> n. TermMeasure G1 = n" (is "\<exists> n. ?P n")
    by auto 
  then obtain n where 1: "?P n" by blast
  have 2: "\<And> G. finiteCFG G \<and> TermMeasure G = n \<Longrightarrow> transformTerm_dom (Gen, G)"
    apply (induction n rule: less_induct)
    using TermTerminate_Part9 a by blast
  from 2 show ?thesis
    by (simp add: "1" b)
qed

lemma TermTerminate_Part11:
  fixes      f :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  fixes      Gen :: "('n, 't) NTGen"
  assumes a: "\<And> G. (TermMeasure G < n \<and> finiteCFG G) \<Longrightarrow> f G (transformTerm Gen G)"
  assumes b: "TermMeasure G = n"
  assumes c: "finiteCFG G"
  assumes d: "NewNTGen Gen"
  assumes e: "\<And> G1 N G2. transformTermTest G1 N G2 \<Longrightarrow> f G1 G2"
  assumes h: "reflp f \<and> transp f"
  shows      "f G (transformTerm Gen G)"
proof-
 show ?thesis
  proof cases
    assume x: "n = 0"
    from x  and b have 0: "transformTerm Gen G = G"
      by (simp add: TermTerminate_Part10 c d transformTerm.psimps)
    from 0 show ?thesis
      by (simp add: h reflpD)
  next
    assume y: "\<not> (n = 0)"
    from y have x: "n > 0" by auto
    from b and x have 0: "TermMeasure G > 0" by auto
    have 1: "\<And> G2. transformTermTest G (Gen G) G2 \<Longrightarrow> TermMeasure G2 < n  \<and> finiteCFG G2"
      using TermTerminate_Part7 and TermTerminate_Part8 
      using b c d by blast
    have 2: "\<exists> G2. transformTermTest G (Gen G) G2"
      using TermTerminate_Part7 and TermTerminate_Part8 
      using "0" d by blast
    from e have 3: "\<And> G2. transformTermTest G (Gen G) G2 \<Longrightarrow> f G G2"
      by blast 
    from 3 and 2 have 4: "f G ((SOME G2. transformTermTest G (Gen G) G2))"
      by (simp add: someI_ex)
    show ?thesis
      by (metis (no_types, lifting) "0" "1" "2" "4" TermTerminate_Part10 a c d h 
            not_less_iff_gr_or_eq someI_ex transformTerm.psimps transpE)
  qed
qed

lemma TermTerminate_Part12:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  assumes c: "\<And> G1 N G2. transformTermTest G1 N G2 \<Longrightarrow> f G1 G2"
  assumes d: "reflp f \<and> transp f"
  shows      "f G1 (transformTerm Gen G1)"
proof-
  have 0: "\<exists> n. TermMeasure G1 = n" (is "\<exists> n. ?P n")
    by auto 
  then obtain n where 1: "?P n" by blast
  have 2: "\<And> G. finiteCFG G \<and> TermMeasure G = n \<Longrightarrow> f G (transformTerm Gen G)"
    apply (induction n rule: less_induct)
    using TermTerminate_Part11 a c 
    by (metis d)
  from 2 show ?thesis
    by (simp add: "1" b)
qed

lemma TermTerminate_Part13:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  shows      "\<lbrakk>transformTerm Gen G1\<rbrakk> = \<lbrakk>G1\<rbrakk>"
proof-
  have 0: "\<And> G1 N G2. transformTermTest G1 N G2 \<Longrightarrow> \<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
    by (meson verifyTransformTermTest)
  from a b 0 show ?thesis
    using TermTerminate_Part12 apply (rule_tac Gen="Gen" in TermTerminate_Part12) 
    apply blast
    apply blast
    apply (simp add: "0")
    by (simp add: reflpI transpI)
qed

definition finiteRel :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "finiteRel G1 G2 \<equiv> finiteCFG G1 \<longrightarrow> finiteCFG G2"

lemma rtransFiniteRel: 
  shows "transp finiteRel \<and> reflp finiteRel"
proof-
  show ?thesis
    apply (unfold finiteRel_def) 
    by (metis (mono_tags, lifting) reflpI transpI)
qed

definition TermProperty :: "('n, 't) CFG \<Rightarrow> bool"
  where "TermProperty G \<equiv> (\<forall> R a. (R \<in> (snd G) \<and> (T a) \<in> set (snd R) \<longrightarrow> (snd R) = [T a]))"

lemma TermTerminate_Part14:
  assumes a: "R \<in> (snd G)"
  assumes b: "CountNonSingleTerminals R > 0"
  assumes c: "finiteCFG G"
  shows      "TermMeasure G > 0"
proof-
  have 0: "\<And> Rs. comp_fun_commute_on Rs TermFold "
    apply (unfold comp_fun_commute_on_def TermFold_def) 
    by fastforce
  from a and 0 have 1: "Finite_Set.fold TermFold 0 (snd G) = TermFold R (Finite_Set.fold TermFold 0 ((snd G) - {R}))"
    by (metis c finiteCFG_def foldRemove)
  from 1 and b have 2: "Finite_Set.fold TermFold 0 (snd G) > 0"
    by (unfold TermFold_def, simp)
  from 2 show ?thesis
    by (unfold TermMeasure_def TermRuleMeasure_def, auto)
qed

lemma TermTerminate_Part15:
  assumes a: "TermMeasure G = 0"
  assumes b: "finiteCFG G"
  shows      "TermProperty G"
proof-
  from a and b have 0: "\<And> R. R \<in> (snd G) \<Longrightarrow> CountNonSingleTerminals R = 0"
    using TermTerminate_Part14 bot_nat_0.not_eq_extremum by blast
  have 1: "\<And> R a. CountNonSingleTerminals R = 0 \<Longrightarrow> (T a) \<in> set (snd R) \<longrightarrow> (snd R) = [T a]"
    by (metis CountProperty2 Nil_is_append_conv append_self_conv2 eq_snd_iff 
        in_set_conv_decomp_last zero_eq_add_iff_both_eq_0 zero_neq_one)
  from 0 and 1 show ?thesis
    apply (unfold TermProperty_def) 
    by (simp add: "1")
qed

lemma TermTerminate_Part16:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG (transformTerm Gen G1)"
proof-
  have 0: "\<And> G1 N G2. transformTermTest G1 N G2 \<Longrightarrow> finiteRel G1 G2"
    by (simp add: finiteRel_def TermFinite)
  from a b 0 have 1: "finiteRel G1 (transformTerm Gen G1)"
    using TermTerminate_Part12 apply (rule_tac Gen="Gen" in TermTerminate_Part12) 
    apply blast
    apply blast
    apply blast
    using rtransFiniteRel by blast
  from 1 and b show ?thesis 
    by (unfold finiteRel_def, auto)
qed

theorem verifyTerm:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG (transformTerm Gen G1) \<and> TermProperty (transformTerm Gen G1) \<and> \<lbrakk>transformTerm Gen G1\<rbrakk> = \<lbrakk>G1\<rbrakk>"
proof-
  from a and b have 0: "transformTerm_dom (Gen, G1)"
    by (simp add: TermTerminate_Part10)
  from 0 have 1: "TermMeasure (transformTerm Gen G1) = 0"
    apply (induct rule: transformTerm.pinduct)
    by (simp add: transformTerm.psimps)
  from 0 have 2: "\<lbrakk>(transformTerm Gen G1)\<rbrakk> = \<lbrakk>G1\<rbrakk>"
    by (simp add: TermTerminate_Part13 a b)
  from b have 3: "finiteCFG (transformTerm Gen G1)"
    by (simp add: TermTerminate_Part16 a)
  from 3 and 1 have 4: "TermProperty (transformTerm Gen G1)"
    using TermTerminate_Part15 by blast
  show ?thesis
    using "2" "3" "4" by fastforce
qed

definition CountMoreThanTwoLists :: "('n, 't) Rule \<Rightarrow> nat"
  where "CountMoreThanTwoLists R = (if length (snd R) < 2 then 0 else (length (snd R) - 2))"

definition BinFold :: "('n, 't) Rule \<Rightarrow> nat \<Rightarrow> nat"
  where "BinFold R N = N + (CountMoreThanTwoLists R)"

definition BinRuleMeasure :: "('n, 't) RuleSet \<Rightarrow> nat"
  where "BinRuleMeasure R = Finite_Set.fold BinFold 0 R"

definition BinMeasure :: "('n, 't) CFG \<Rightarrow> nat"
  where "BinMeasure G = BinRuleMeasure (snd G)"

lemma BinTerminate_Part1:
  assumes x: "transformBinTest G1 N G2"
  assumes y: "finiteCFG G1"
  shows      "BinMeasure G1 > BinMeasure G2"
proof-
  from x have 1: "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
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
    by (simp add: transformBinTest_def)
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
  from a b c d have 2: "CountMoreThanTwoLists R2 + CountMoreThanTwoLists R3 < CountMoreThanTwoLists R1"
    apply (simp add: CountMoreThanTwoLists_def) 
    by (metis Nat.add_diff_assoc One_nat_def Suc_pred add_eq_if add_le_cancel_left length_0_conv length_greater_0_conv lessI plus_1_eq_Suc zero_le)  
  from y and e have 0: "finite Rs1" by (simp add: finiteCFG_def)
  have 4: "\<And> Rs. comp_fun_commute_on Rs BinFold "
    apply (unfold comp_fun_commute_on_def BinFold_def) 
    by fastforce
  from 4 and i and 0 have 5: "BinFold R1 (BinRuleMeasure (Rs1 - {R1})) = BinRuleMeasure Rs1"
    apply (unfold BinRuleMeasure_def)
    by (simp add: "4" foldRemove)
  from 5 have 6: "CountMoreThanTwoLists R1 + (BinRuleMeasure (Rs1 - {R1})) = BinRuleMeasure Rs1"
    by (unfold BinFold_def, auto)
  from b and k have 7: "R2 \<notin> Rs1"
    apply (unfold NonTerminals_def NTInRule_def)
    using e by fastforce
  from c and k have 8: "R3 \<notin> Rs1"
    apply (unfold NonTerminals_def NTInRule_def)
    using e  by auto
  from 7 have 9: "R2 \<notin> (Rs1 - {R1})"
    by auto
  from 9 and 0 and 4 have 10: "BinFold R2 (BinRuleMeasure (Rs1 - {R1})) = BinRuleMeasure ({R2} \<union> (Rs1 - {R1}))"
    by (metis BinRuleMeasure_def finite_Diff  foldInsert insert_is_Un)
  from 10 have 11: "CountMoreThanTwoLists R2 + (BinRuleMeasure (Rs1 - {R1})) = BinRuleMeasure ({R2} \<union> (Rs1 - {R1}))"
    by (simp add: BinFold_def)
  from 8 have 12: "R3 \<notin> {R2} \<union> (Rs1 - {R1})"
    by (smt (verit, del_insts) Diff_iff NTInRule_def NonTerminals_def Pair_inject insert_iff insert_is_Un mem_Collect_eq r)
  from 12 and 4 have 13: "BinFold R3 (BinRuleMeasure ({R2} \<union> (Rs1 - {R1}))) = BinRuleMeasure ({R2, R3} \<union> (Rs1 - {R1}))"
    by (smt (verit) "0" BinRuleMeasure_def Un_insert_left finite_Diff finite_insert foldInsert insert_commute sup_bot_left)
  from 13 and 12 have 14: "CountMoreThanTwoLists R3 + CountMoreThanTwoLists R2 + (BinRuleMeasure (Rs1 - {R1})) = BinRuleMeasure (Rs2)"
    by (metis "11" BinFold_def ab_semigroup_add_class.add_ac(1) add.commute j)
  from 14 and 6 and 2 show ?thesis
    by (simp add: BinMeasure_def e f)
qed

lemma BinTerminate_Part2:
  assumes a: "\<And> R. R \<in> Rs \<Longrightarrow> CountMoreThanTwoLists R = 0"
  assumes b: "finite Rs"
  shows      "fold_graph BinFold 0 Rs 0"
proof-
  have 0: "\<And> Rs. comp_fun_commute_on Rs BinFold "
    apply (unfold comp_fun_commute_on_def BinFold_def) 
    by fastforce
  from 0 have 1: "comp_fun_commute_on Rs BinFold" by auto
  have 2: "finite Rs \<Longrightarrow> (\<And> R. R \<in> Rs \<Longrightarrow> CountMoreThanTwoLists R = 0) \<Longrightarrow> fold_graph BinFold 0 Rs 0"
    apply (induct rule: finite_induct) 
    using fold_graph.emptyI apply fastforce
    by (metis BinFold_def add.right_neutral fold_graph.insertI insertCI)
  from 2 show ?thesis
    using a b by blast
qed

lemma BinTerminate_Part3:
  assumes a: "\<And> R. R \<in> Rs \<Longrightarrow> CountMoreThanTwoLists R = 0"
  assumes b: "finite Rs"
  shows      "BinRuleMeasure Rs = 0"
proof-
  from a and b have 0: "fold_graph BinFold 0 Rs 0"
    using BinTerminate_Part2 by blast
  from b and 0 have 1: "\<And> x. fold_graph BinFold 0 Rs x \<Longrightarrow> x = 0"
    by (smt (verit) BinFold_def a empty_iff fold_graph_closed_lemma insert_iff plus_nat.add_0)
  from b and 1 show ?thesis
    apply (unfold BinRuleMeasure_def Finite_Set.fold_def, auto)
    using "0" by blast
qed

lemma BinTerminate_Part4:
  assumes a: "CountMoreThanTwoLists R > 0"
  shows      "\<exists> l r a. snd R = l @ a # r \<and> l \<noteq> [] \<and> r \<noteq> []"
proof-
  from a have 0: "length (snd R) \<ge> 3"
    apply (unfold CountMoreThanTwoLists_def) 
    by (metis (mono_tags, opaque_lifting) One_nat_def Suc_eq_plus1 Suc_leI cancel_comm_monoid_add_class.diff_cancel
        linorder_less_linear numeral_3_eq_3 one_add_one zero_less_iff_neq_zero)
  from 0 show ?thesis
    by (metis (no_types, opaque_lifting) append_Cons append_Nil dual_order.strict_iff_not 
        length_Cons list.exhaust list.size(3) not_less_eq numeral_3_eq_3)
qed

lemma BinTerminate_Part5:
  assumes a: "BinMeasure G1 > 0"
  assumes b: "(NT N) \<notin> NonTerminals G1"
  shows      "\<exists> G2. transformBinTest G1 N G2"
proof-
  from a have 0: "\<exists> R. R \<in> snd G1 \<and> CountMoreThanTwoLists R > 0" (is "\<exists> R. ?P R")
    apply (unfold BinMeasure_def) 
    by (metis Finite_Set.fold_def BinRuleMeasure_def 
        BinTerminate_Part3 bot_nat_0.not_eq_extremum) 
  then obtain R where 1: "?P R" by blast
  from 1 have 2: "\<exists> l r a S1 rhs. rhs = l @ a # r \<and> l \<noteq> [] \<and> r \<noteq> [] \<and> (S1, rhs) = R" 
    (is "\<exists> l r t S1 rhs. ?P l r t S1 rhs")
    by (metis BinTerminate_Part4 old.prod.exhaust snd_conv)
  then obtain l r a S1 rhs where 3: "?P l r a S1 rhs" by blast
  have 4: "\<exists> Rs1 S. (S, Rs1) = G1" (is "\<exists> Rs1 S. ?P Rs1 S")
    using prod.collapse by blast
  then obtain Rs1 S where 5: "?P Rs1 S" by blast
  from 5 and 3 and b show ?thesis
    apply (unfold transformBinTest_def , rule_tac x="(S, ({(S1, l @ [NT N]), (N, a # r)} \<union> (Rs1-{R})))" in exI, simp
          , rule_tac x="S" in exI, simp,rule_tac x="S1" in exI, simp, rule_tac x="rhs" in exI, simp,
          rule_tac x="l @ [NT N]" in exI, simp, rule_tac x="Rs1" in exI, simp) 
    using "1" by fastforce
qed

function (domintros) transformBin :: "('n, 't) NTGen \<Rightarrow> ('n, 't) CFG \<Rightarrow> ('n, 't) CFG"
  where "transformBin Gen G1 = (if (BinMeasure G1 = 0) then G1 else 
                                (transformBin Gen (SOME G2. transformBinTest G1 (Gen G1) G2)))"
  by pat_completeness auto

lemma BinTerminate_Part7:
  assumes a: "finiteCFG G"
  shows      "\<forall> G2. (transformBinTest G (Gen G) G2 \<longrightarrow> finiteCFG G2 \<and> BinMeasure G2 < BinMeasure G)"
proof-
  from a show ?thesis 
    by (simp add: BinFinite BinTerminate_Part1)
qed

lemma BinTerminate_Part8:
  assumes a: "BinMeasure G > 0"
  assumes b: "NewNTGen Gen"
  shows      "\<exists> G2. (transformBinTest G (Gen G) G2)"
proof-
  from b have 0: "(NT (Gen G)) \<notin> NonTerminals G"
    using NewNTGen_def by blast
  from 0 and a show ?thesis
    by (meson BinTerminate_Part5)
qed

lemma BinTerminate_Part9:
  assumes d: "NewNTGen Gen"
  assumes a: "\<And> G. (BinMeasure G < n \<and> finiteCFG G) \<Longrightarrow> transformBin_dom (Gen, G)"
  assumes b: "BinMeasure G = n"
  assumes c: "finiteCFG G"
  shows      "transformBin_dom (Gen, G)"
proof-
  show ?thesis
  proof cases
    assume x: "n = 0"
    have 0: "\<And> G gen. BinMeasure G = 0 \<Longrightarrow> transformBin_dom (gen, G)"
      apply (rule transformBin.domintros)
      by fastforce
    from x and 0 and b show ?thesis by blast
  next
    assume y: "n \<noteq> 0"
    from y have x: "n > 0" by auto
    from b and x have 0: "BinMeasure G > 0" by auto
    have 1: "\<And> G2. transformBinTest G (Gen G) G2 \<Longrightarrow> BinMeasure G2 < n  \<and> finiteCFG G2"
      using BinTerminate_Part7 and BinTerminate_Part8 
      using b c d by blast
    have 2: "\<exists> G2. transformBinTest G (Gen G) G2"
      using BinTerminate_Part7 and BinTerminate_Part8 
      using "0" d by blast
    from a and 1 and d have 3: "\<And> G2. transformBinTest G (Gen G) G2 \<Longrightarrow> transformBin_dom (Gen, G2)"
      by blast
    from 3 and 2 have 4: "transformBin_dom (Gen, (SOME G2. transformBinTest G (Gen G) G2))"
      by (simp add: someI_ex)
    from 0 and 4 show ?thesis
      by (meson transformBin.domintros)
  qed
qed

lemma BinTerminate_Part10:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  shows      "transformBin_dom (Gen, G1)"
proof-
  have 0: "\<exists> n. BinMeasure G1 = n" (is "\<exists> n. ?P n")
    by auto 
  then obtain n where 1: "?P n" by blast
  have 2: "\<And> G. finiteCFG G \<and> BinMeasure G = n \<Longrightarrow> transformBin_dom (Gen, G)"
    apply (induction n rule: less_induct)
    using BinTerminate_Part9 a by blast
  from 2 show ?thesis
    by (simp add: "1" b)
qed

lemma BinTerminate_Part11:
  fixes      f :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  fixes      Gen :: "('n, 't) NTGen"
  assumes a: "\<And> G. (BinMeasure G < n \<and> finiteCFG G) \<Longrightarrow> f G (transformBin Gen G)"
  assumes b: "BinMeasure G = n"
  assumes c: "finiteCFG G"
  assumes d: "NewNTGen Gen"
  assumes e: "\<And> G1 N G2. transformBinTest G1 N G2 \<Longrightarrow> f G1 G2"
  assumes h: "reflp f \<and> transp f"
  shows      "f G (transformBin Gen G)"
proof-
 show ?thesis
  proof cases
    assume x: "n = 0"
    from x  and b have 0: "transformBin Gen G = G"
      by (simp add: BinTerminate_Part10 c d transformBin.psimps)
    from 0 show ?thesis
      by(simp add: h reflpD)
  next
    assume y: "\<not> (n = 0)"
    from y have x: "n > 0" by auto
    from b and x have 0: "BinMeasure G > 0" by auto
    have 1: "\<And> G2. transformBinTest G (Gen G) G2 \<Longrightarrow> BinMeasure G2 < n  \<and> finiteCFG G2"
      using BinTerminate_Part7 and BinTerminate_Part8 
      using b c d by blast
    have 2: "\<exists> G2. transformBinTest G (Gen G) G2"
      using BinTerminate_Part7 and BinTerminate_Part8 
      using "0" d by blast
    from e have 3: "\<And> G2. transformBinTest G (Gen G) G2 \<Longrightarrow> f G G2"
      by blast 
    from 3 and 2 have 4: "f G ((SOME G2. transformBinTest G (Gen G) G2))"
      by (metis someI_ex)
    show ?thesis
      by (metis (no_types, lifting) "0" "2" "4" BinTerminate_Part10 
          BinTerminate_Part7 a b c d h someI_ex transformBin.psimps transpE)
  qed
qed

lemma BinTerminate_Part12:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  assumes c: "\<And> G1 N G2. transformBinTest G1 N G2 \<Longrightarrow> f G1 G2"
  assumes h: "reflp f \<and> transp f"
  shows      "f G1 (transformBin Gen G1)"
proof-
have 0: "\<exists> n. BinMeasure G1 = n" (is "\<exists> n. ?P n")
    by auto 
  then obtain n where 1: "?P n" by blast
  have 2: "\<And> G. finiteCFG G \<and> BinMeasure G = n \<Longrightarrow> f G (transformBin Gen G)"
    apply (induction n rule: less_induct)
    using BinTerminate_Part11 a c 
    by (metis h)
  from 2 show ?thesis
    by (simp add: "1" b)
qed

lemma BinTerminate_Part13:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  shows      "\<lbrakk>transformBin Gen G1\<rbrakk> = \<lbrakk>G1\<rbrakk>"
proof-
  have 0: "\<And> G1 N G2. transformBinTest G1 N G2 \<Longrightarrow> \<lbrakk>G1\<rbrakk> = \<lbrakk>G2\<rbrakk>"
    by (simp add: verifyTransformBinTest)
  from a b 0 show ?thesis
    using BinTerminate_Part12 apply (rule_tac Gen="Gen" in BinTerminate_Part12, simp)
    apply blast
    apply (simp add: "0")
    by (simp add: reflpI transpI)
qed

definition BinProperty :: "('n, 't) CFG \<Rightarrow> bool"
  where "BinProperty G \<equiv> (\<forall> R. (R \<in> (snd G) \<longrightarrow> length (snd R) \<le> 2 ))"

lemma BinTerminate_Part14:
  assumes a: "R \<in> (snd G)"
  assumes b: "CountMoreThanTwoLists R > 0"
  assumes c: "finiteCFG G"
  shows      "BinMeasure G > 0"
proof-
  have 0: "\<And> Rs. comp_fun_commute_on Rs BinFold "
    apply (unfold comp_fun_commute_on_def BinFold_def) 
    by fastforce
  from a and 0 have 1: "Finite_Set.fold BinFold 0 (snd G) = BinFold R (Finite_Set.fold BinFold 0 ((snd G) - {R}))"
    by (metis c finiteCFG_def foldRemove)
  from 1 and b have 2: "Finite_Set.fold BinFold 0 (snd G) > 0"
    by (unfold BinFold_def, simp)
  from 2 show ?thesis
    by (unfold BinMeasure_def BinRuleMeasure_def, auto)
qed

lemma BinTerminate_Part15:
  assumes a: "BinMeasure G = 0"
  assumes b: "finiteCFG G"
  shows      "BinProperty G"
proof-
  from a and b have 0: "\<And> R. R \<in> (snd G) \<Longrightarrow> CountMoreThanTwoLists R = 0"
    using BinTerminate_Part14 bot_nat_0.not_eq_extremum by blast
  have 1: "\<And> R. CountMoreThanTwoLists R = 0 \<Longrightarrow> length (snd R) \<le> 2 "
    by (metis CountMoreThanTwoLists_def diff_is_0_eq dual_order.strict_iff_not)
  from 0 and 1 show ?thesis
    apply (unfold BinProperty_def) 
    by (simp add: "1")
qed

lemma BinTerminate_Part16:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG (transformBin Gen G1)"
proof-
  have 0: "\<And> G1 N G2. transformBinTest G1 N G2 \<Longrightarrow> finiteRel G1 G2"
    by (simp add: finiteRel_def BinFinite)
  from a b 0 have 1: "finiteRel G1 (transformBin Gen G1)"
    using BinTerminate_Part12 apply (rule_tac Gen="Gen" in BinTerminate_Part12) 
    apply blast
    apply blast
    apply blast
    using rtransFiniteRel by blast
  from 1 and b show ?thesis 
    by (unfold finiteRel_def, auto)
qed

theorem verifyBin:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  shows      "finiteCFG (transformBin Gen G1) \<and>  BinProperty (transformBin Gen G1) \<and> \<lbrakk>transformBin Gen G1\<rbrakk> = \<lbrakk>G1\<rbrakk>"
proof-
  from a and b have 0: "transformBin_dom (Gen, G1)"
    by (simp add: BinTerminate_Part10)
  from 0 have 1: "BinMeasure (transformBin Gen G1) = 0"
    apply (induct rule: transformBin.pinduct)
    by (simp add: transformBin.psimps)
  from 0 have 2: "\<lbrakk>(transformBin Gen G1)\<rbrakk> = \<lbrakk>G1\<rbrakk>"
    by (simp add: BinTerminate_Part13 a b)
  from b have 3: "finiteCFG (transformBin Gen G1)"
    by (simp add: BinTerminate_Part16 a)
  from 3 and 1 have 4: "BinProperty (transformBin Gen G1)"
    using BinTerminate_Part15 by blast
  show ?thesis
    using "2" "3" "4" by fastforce
qed

definition UnitFold :: "('n, 't) RuleSet \<Rightarrow> 'n \<Rightarrow> nat \<Rightarrow> nat"
  where "UnitFold Rs N n = n + (if (HasUnitProductionRule Rs N) then 1 else 0)"

definition UnitRuleMeasure :: "('n, 't) RuleSet \<Rightarrow> nat"
  where "UnitRuleMeasure Rs = Finite_Set.fold (UnitFold Rs) 0 (image fst Rs)"

definition UnitMeasure :: "('n, 't) CFG \<Rightarrow> nat"
  where "UnitMeasure G = UnitRuleMeasure (snd G)"

lemma UnitTerminate_Part1:
  assumes x: "transformUnitTest G1 N G2"
  assumes y: "finiteCFG G1"
  shows      "UnitMeasure G1 > UnitMeasure G2"
proof-
  from x have 0: "\<exists> S Rs1 Rs2. 
                  (S, Rs1) = G1
                  \<and> (S, Rs2) = G2
                  \<and> HasUnitProductionRule Rs1 N
                  \<and> Rs2 = (Rs1 \<union> (NewUnitTransRuleSet N Rs1)) - (NTToNTSetForA N)"
          (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformUnitTest_def)
  then obtain S Rs1 Rs2 where r: "?P S Rs1 Rs2" by blast
  from r have a: "G1 = (S, Rs1)" by auto
  from r have b: "G2 = (S, Rs2)" by auto
  from r have c: "HasUnitProductionRule Rs1 N" by auto
  from r have d: "Rs2 = (Rs1 \<union> (NewUnitTransRuleSet N Rs1)) - (NTToNTSetForA N)" by auto
  from d have 1: "\<not> HasUnitProductionRule Rs2 N"
    apply (unfold HasUnitProductionRule_def IsUnitProductionRule_def NTToNTSetForA_def) 
    by force
  from d have 2: "\<And> A rhs. A \<noteq> N \<Longrightarrow> (A, rhs) \<in> Rs1 \<longleftrightarrow>(A, rhs) \<in> Rs2"
    apply (unfold NewUnitTransRuleSet_def NTToNTSetForA_def) 
    by blast
  from 2 have 3: "\<And> A. A \<noteq> N \<Longrightarrow> HasUnitProductionRule Rs1 A \<longleftrightarrow> HasUnitProductionRule Rs2 A"
    apply (unfold HasUnitProductionRule_def) 
    by auto
  from 2 have 4: "\<And> A rhs. A \<noteq> N \<Longrightarrow> A \<in> image fst Rs2 \<longleftrightarrow> A \<in> image fst Rs1"
    by auto
  from c have 5: "N \<in> image fst Rs1"
    apply (unfold HasUnitProductionRule_def) by blast
  from 4 and 5 have 6: "image fst Rs2 \<union> {N} = image fst Rs1"
    by auto
  have 7: "\<And> Rs x. comp_fun_commute_on x (UnitFold Rs)"
    apply (unfold comp_fun_commute_on_def UnitFold_def) 
    by (auto)
  from y have 8: "finite (image fst Rs1)"
    by (unfold finiteCFG_def, simp add: a)
  from 5 and a and 7 and 8 have 9: "(UnitFold Rs1) N (Finite_Set.fold (UnitFold Rs1) 0 ((image fst Rs1) - {N})) = UnitMeasure G1"
    apply (unfold UnitMeasure_def UnitRuleMeasure_def, simp) 
    by (simp add: "7" foldRemove)
  from 9 and c have 10: "UnitMeasure G1 = (Finite_Set.fold (UnitFold Rs1) 0 ((image fst Rs1) - {N})) + 1"
    by (unfold UnitFold_def, auto)
  from 6 have 11: "image fst Rs2 - {N} = image fst Rs1 - {N}" by auto
  from x and y have 12: "finiteCFG G2" 
    by (simp add: UnitFinite)
  from 12 have 13: "finite (image fst Rs2)"
    by (unfold finiteCFG_def, simp add: b)
  show ?thesis
  proof cases
    assume x: "N \<in> image fst Rs2"
    from 7 and 13 and x and b have 14: "(UnitFold Rs2) N (Finite_Set.fold (UnitFold Rs2) 0 ((image fst Rs2) - {N})) = UnitMeasure G2"
      by (metis UnitMeasure_def UnitRuleMeasure_def foldRemove prod.sel(2))
    from 1 and 14 have 15: "UnitMeasure G2 = (Finite_Set.fold (UnitFold Rs2) 0 ((image fst Rs2) - {N}))" 
      by (simp add: UnitFold_def)
    from 3 have 16: "\<And> x. x \<in> ((image fst Rs2) - {N}) \<Longrightarrow> ((UnitFold Rs1 x) = (UnitFold Rs2 x))"
      apply (unfold UnitFold_def)
      by simp
    from 15 and 3 have 17: "UnitMeasure G2 = (Finite_Set.fold (UnitFold Rs1) 0 ((image fst Rs2) - {N}))" 
      by (smt (verit, ccfv_SIG) "13" "16" "7" Diff_subset Finite_Set.fold_cong finite_Diff)
    from 17 and 11 and 10 show ?thesis by force
  next
    assume x: "N \<notin> image fst Rs2"
    from x have 14: "(Finite_Set.fold (UnitFold Rs2) 0 ((image fst Rs2) - {N})) = UnitMeasure G2"
      by (simp add: UnitMeasure_def UnitRuleMeasure_def b)
    from 3 have 15: "\<And> x. x \<in> ((image fst Rs2) - {N}) \<Longrightarrow> ((UnitFold Rs1 x) = (UnitFold Rs2 x))"
      apply (unfold UnitFold_def)
      by simp
    from 14 and 3 have 16: "UnitMeasure G2 = (Finite_Set.fold (UnitFold Rs1) 0 ((image fst Rs2) - {N}))" 
      by (smt (verit, ccfv_SIG) "13" "15" "7" Diff_subset Finite_Set.fold_cong finite_Diff)
    from 16 and 11 and 10 show ?thesis by force
  qed
qed

lemma UnitTerminate_Part2:
  assumes a: "\<And> N. N \<in> (image fst Rs) \<Longrightarrow> \<not> HasUnitProductionRule Rs N"
  assumes b: "finite (fst ` Rs)"
  shows      "fold_graph (UnitFold Rs) 0 (image fst Rs) 0"
proof-
  have 0: "\<And> Rs x. comp_fun_commute_on x (UnitFold Rs) "
    apply (unfold comp_fun_commute_on_def UnitFold_def) 
    by fastforce
  from 0 have 1: "comp_fun_commute_on (image fst Rs) (UnitFold Rs)" by auto
  have 2: "finite (image fst Rs) \<Longrightarrow> (\<And> N. N \<in> (image fst Rs) \<Longrightarrow> \<not> HasUnitProductionRule Rs N) \<Longrightarrow> fold_graph (UnitFold Rs) 0 (image fst Rs) 0"
    apply (induct rule: finite_induct) 
    using fold_graph.emptyI apply fastforce
    by (metis (full_types) UnitFold_def add.right_neutral fold_graph.simps insertCI)
  from 2 show ?thesis
    using a b by blast
qed

lemma UnitTerminate_Part3:
  assumes a: "\<And> N. N \<in> (image fst Rs) \<Longrightarrow> \<not> HasUnitProductionRule Rs N"
  assumes b: "finite (fst ` Rs)"
  shows      "UnitRuleMeasure Rs = 0"
proof-
  from a and b have 0: "fold_graph (UnitFold Rs) 0 (image fst Rs) 0"
    using UnitTerminate_Part2 by blast
  from b have 1: "finite (image fst Rs)" by auto
  from 1 and 0 have 2: "\<And> x. fold_graph (UnitFold Rs) 0 (image fst Rs) x \<Longrightarrow> x = 0"
    by (smt (verit, ccfv_threshold) UnitFold_def UnitTerminate_Part2 a add.right_neutral 
        empty_fold_graphE empty_iff finite.emptyI fold_graph_closed_lemma image_empty mem_Collect_eq)
  from 0 and 2 and b show ?thesis
    apply (unfold UnitRuleMeasure_def Finite_Set.fold_def, simp) 
    by blast
qed

lemma UnitTerminate_Part4:
  assumes a: "UnitRuleMeasure Rs > 0"
  shows      "\<exists> N. N \<in> (image fst Rs) \<and> HasUnitProductionRule Rs N"
proof-
  from a have 0: "finite (fst ` Rs)" 
    apply (unfold UnitRuleMeasure_def Finite_Set.fold_def)
    by presburger
  from 0 show ?thesis 
    by (metis UnitTerminate_Part3 assms bot_nat_0.not_eq_extremum)
qed

lemma UnitTerminate_Part5:
  assumes a: "UnitMeasure G1 > 0"
  shows      "\<exists> A G2. transformUnitTest G1 A G2"
proof-
  from a have 0: "\<exists> N. HasUnitProductionRule (snd G1) N" (is "\<exists> N. ?P N")
    by (metis UnitMeasure_def UnitTerminate_Part4)
  then obtain N where 1: "?P N" by blast
  from 1 show ?thesis
    by (unfold transformUnitTest_def, rule_tac x="N" in exI, simp, rule_tac x="fst G1" in exI, simp, rule_tac x="snd G1" in exI, simp)
qed

function (domintros) transformUnit :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG"
  where "transformUnit G1 = (if (UnitMeasure G1 = 0) then G1 else 
                            (transformUnit (SOME G2. \<exists> A. transformUnitTest G1 A G2)))"
  by pat_completeness auto

lemma UnitTerminate_Part7:
  assumes a: "finiteCFG G"
  shows      "\<forall> A G2. (transformUnitTest G A G2 \<longrightarrow> finiteCFG G2 \<and> UnitMeasure G2 < UnitMeasure G)"
proof-
  from a show ?thesis 
    by (simp add: UnitFinite UnitTerminate_Part1)
qed

lemma UnitTerminate_Part9:
  fixes      G :: "('n, 't) CFG"
  assumes a: "\<And> G2 :: ('n, 't) CFG. ((UnitMeasure G2 < n \<and> finiteCFG G2) \<Longrightarrow> transformUnit_dom (G2))"
  assumes b: "UnitMeasure G = n"
  assumes c: "finiteCFG G"
  shows      "transformUnit_dom G"
proof-
  show ?thesis
  proof cases
    assume x: "n = 0"
    have 0: "\<And> G . UnitMeasure G = 0 \<Longrightarrow> transformUnit_dom G"
      apply (rule transformUnit.domintros)
      by fastforce
    from x and 0 and b show ?thesis by blast
  next
    assume y: "n \<noteq> 0"
    from y have x: "n > 0" by auto
    from b and x have 0: "UnitMeasure G > 0" by auto
    have 1: "\<And> A G2. transformUnitTest G A G2 \<Longrightarrow> (UnitMeasure G2 < n  \<and> finiteCFG G2)"
      using UnitTerminate_Part7 and c and b by blast
    have 2: "\<exists> A G2. transformUnitTest G A G2" 
      using UnitTerminate_Part5 and 0 by blast
    from 1 and a have 3: "\<And> A G2. (transformUnitTest G A G2 \<Longrightarrow> transformUnit_dom G2)"
      by blast
    from 3 and 2 have 4: "transformUnit_dom (SOME G2. \<exists> A. transformUnitTest G A G2)"
      by (smt (verit) someI_ex)
    from 0 and 4 show ?thesis
      by (metis transformUnit.domintros)
  qed
qed
      
lemma UnitTerminate_Part10:
  assumes b: "finiteCFG G1"
  shows      "transformUnit_dom G1"
proof-
  have 0: "\<exists> n. UnitMeasure G1 = n" (is "\<exists> n. ?P n")
    by auto 
  then obtain n where 1: "?P n" by blast
  have 2: "\<And> G. finiteCFG G \<and> UnitMeasure G = n \<Longrightarrow> transformUnit_dom (G)"
    apply (induction n rule: less_induct)
    using UnitTerminate_Part9 by blast
  from 2 show ?thesis
    using "1" b by blast
qed

lemma UnitTerminate_Part11:
  fixes      f :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  fixes      Gen :: "('n, 't) NTGen"
  assumes a: "\<And> G. (UnitMeasure G < n \<and> finiteCFG G) \<Longrightarrow> f G (transformUnit G)"
  assumes b: "UnitMeasure G = n"
  assumes c: "finiteCFG G"
  assumes e: "\<And> G1 N G2. transformUnitTest G1 N G2 \<Longrightarrow> f G1 G2"
  assumes h: "reflp f \<and> transp f"
  shows      "f G (transformUnit G)"
proof-
   show ?thesis
  proof cases
    assume x: "n = 0"
    from x  and b have 0: "transformUnit G = G"
      by (simp add: UnitTerminate_Part10 c transformUnit.psimps)
    from 0 show ?thesis
      by (simp add: h reflpD)
  next
    assume y: "\<not> (n = 0)"
    from y have x: "n > 0" by auto
    from b and x have 0: "UnitMeasure G > 0" by auto
    have 1: "\<And> A G2. transformUnitTest G A G2 \<Longrightarrow> UnitMeasure G2 < n  \<and> finiteCFG G2"
      using UnitTerminate_Part7 
      using b c by blast
    have 2: "\<exists> G2 A. transformUnitTest G A G2" 
      using UnitTerminate_Part5 and 0 by blast
    have 3: "\<And> A G2. transformUnitTest G A G2 \<Longrightarrow> f G G2"
      by (simp add: e)  
    from 3 and 2 have 4: "f G (SOME G2. \<exists> A. transformUnitTest G A G2)"
      by (smt (verit) someI_ex)
    from 0 and 4 show ?thesis
      by (smt (verit) "2" UnitTerminate_Part10 UnitTerminate_Part7 a b c e h someI_ex
            some_equality transformUnit.psimps transpE y)
  qed
qed

lemma UnitTerminate_Part12:
  assumes a: "finiteCFG G1"
  assumes b: "\<And> G1 N G2. transformUnitTest G1 N G2 \<Longrightarrow> f G1 G2"
  assumes h: "reflp f \<and> transp f"
  shows      "f G1 (transformUnit G1)"
proof-
  have 0: "\<exists> n. UnitMeasure G1 = n" (is "\<exists> n. ?P n")
    by auto 
  then obtain n where 1: "?P n" by blast
  have 2: "\<And> G. finiteCFG G \<and> UnitMeasure G = n \<Longrightarrow> f G (transformUnit G)"
    apply (induction n rule: less_induct)
    using UnitTerminate_Part11
    by (metis b h)
  from 2 show ?thesis
    using "1" a by blast
qed

lemma UnitTerminate_Part13:
  assumes b: "finiteCFG G"
  shows      "\<lbrakk>transformUnit G\<rbrakk> = \<lbrakk>G\<rbrakk>"
proof-
  have 0: "\<And> G N G2. transformUnitTest G N G2 \<Longrightarrow> \<lbrakk>G\<rbrakk> = \<lbrakk>G2\<rbrakk>"
    by (simp add: verifyTransformUnitTest)
  from 0 b show ?thesis
    using UnitTerminate_Part12 
    by (metis equivLang_def reflpI transp_def)
qed

definition UnitProperty :: "('n, 't) CFG \<Rightarrow> bool"
  where "UnitProperty G \<equiv> \<forall> R. (R \<in> (snd G) \<longrightarrow> \<not> IsUnitProductionRule R)"

lemma UnitTerminate_Part14:
  assumes a: "N \<in> fst `(snd G)"
  assumes b: "HasUnitProductionRule (snd G) N"
  assumes c: "finiteCFG G"
  shows      "UnitMeasure G > 0"
proof-
  have 0: "\<And> Rs. comp_fun_commute_on (fst ` Rs) (UnitFold Rs) "
    apply (unfold comp_fun_commute_on_def UnitFold_def)
    by (simp add: comp_def)
  from a and 0 have 1: "Finite_Set.fold (UnitFold (snd G)) 0 (fst ` (snd G)) = (UnitFold (snd G)) N (Finite_Set.fold (UnitFold (snd G)) 0 (fst ` (snd G) - {N}))"
    by (metis c finiteCFG_def finite_imageI foldRemove)
  from 1 and b have 2: "Finite_Set.fold (UnitFold (snd G)) 0 (fst ` (snd G)) > 0"
    by (unfold UnitFold_def, simp)
  from 2 show ?thesis
    by (unfold UnitMeasure_def UnitRuleMeasure_def, auto)
qed

lemma UnitTerminate_Part15:
  assumes a: "UnitMeasure G = 0"
  assumes b: "finiteCFG G"
  shows      "UnitProperty G"
proof-
  from a and b have 0: "\<And> N. N \<in> fst ` (snd G) \<Longrightarrow> \<not> HasUnitProductionRule (snd G) N"
    using UnitTerminate_Part14 bot_nat_0.not_eq_extremum by metis
  have 1: "\<And> N. \<not> HasUnitProductionRule (snd G) N \<Longrightarrow> \<not> (\<exists>R. R \<in> (snd G) \<and> (fst R) = N \<and> IsUnitProductionRule R)"
    by (unfold HasUnitProductionRule_def, auto)
  from 0 and 1 show ?thesis
    apply (unfold UnitProperty_def) 
    by blast
qed

lemma UnitTerminate_Part16:
  assumes b: "finiteCFG G1"
  shows      "finiteCFG (transformUnit G1)"
proof-
  have 0: "\<And> G1 N G2. transformUnitTest G1 N G2 \<Longrightarrow> finiteRel G1 G2"
    by (simp add: finiteRel_def UnitFinite)
  from b 0 have 1: "finiteRel G1 (transformUnit G1)"
    using UnitTerminate_Part12 
    using "0" b rtransFiniteRel by blast
  from 1 and b show ?thesis 
    by (unfold finiteRel_def, auto)
qed

theorem verifyUnit:
  assumes b: "finiteCFG G1"
  shows      "finiteCFG (transformUnit G1) \<and> UnitProperty (transformUnit G1) \<and> \<lbrakk>transformUnit G1\<rbrakk> = \<lbrakk>G1\<rbrakk>"
proof-
  from  b have 0: "transformUnit_dom G1"
    by (simp add: UnitTerminate_Part10)
  from 0 have 1: "UnitMeasure (transformUnit  G1) = 0"
    apply (induct rule: transformUnit.pinduct)
    by (simp add: transformUnit.psimps)
  from 0 have 2: "\<lbrakk>(transformUnit G1)\<rbrakk> = \<lbrakk>G1\<rbrakk>"
    by (simp add: UnitTerminate_Part13 b)
  from b have 3: "finiteCFG (transformUnit G1)"
    by (simp add: UnitTerminate_Part16)
  from 3 and 1 have 4: "UnitProperty (transformUnit G1)"
    using UnitTerminate_Part15 by blast
  show ?thesis
    using "2" "3" "4" by fastforce
qed

definition StartProperty :: "('n, 't) CFG \<Rightarrow> bool"
  where "StartProperty G \<equiv> (\<forall> R. R \<in> (snd G) \<longrightarrow> (NT (fst G)) \<notin> set (snd R))"

definition DelProperty :: "('n, 't) CFG \<Rightarrow> bool"
  where "DelProperty G \<equiv> (\<forall> R. R \<in> (snd G) \<longrightarrow> (fst R) \<noteq> (fst G) \<longrightarrow> (snd R) \<noteq> [])"

definition transformStart :: "('n, 't) NTGen \<Rightarrow>('n, 't) CFG \<Rightarrow> ('n, 't) CFG" 
  where "transformStart Gen G1 \<equiv> (SOME G2. transformStartTest G1 (Gen G1) G2)"

definition transformDel :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG" 
  where "transformDel G1 \<equiv> (SOME G2. transformDelTest G1 G2)"

lemma StartProp_Part1:
  assumes a: "transformStartTest G1 N G2"
  shows      "StartProperty G2"
proof-
  from a show ?thesis
    by (unfold transformStartTest_def StartProperty_def NonTerminals_def NTInRule_def, auto)
qed

lemma DelProp_Part1:
  assumes a: "transformDelTest G1 G2"
  shows      "DelProperty G2"
proof-
  from a show ?thesis
    by (unfold transformDelTest_def RemoveAllEpsilonProds_def DelProperty_def, auto)
qed

lemma StartProp_Part2:
  assumes a: "NewNTGen Gen"
  shows      "StartProperty (transformStart Gen G1)"
proof-
  have 0: "\<And> N G1. (NT N) \<notin> NonTerminals G1 \<Longrightarrow> \<exists> G2. transformStartTest G1 N G2"
    by (unfold transformStartTest_def, auto)
  from a and 0 have 1: "\<exists> G2. transformStartTest G1 (Gen G1) G2"
    apply (unfold NewNTGen_def) 
    by (meson "0")
  from StartProp_Part1 and 1 show ?thesis
    apply (unfold transformStart_def) 
    by (smt (verit, ccfv_threshold) StartProp_Part1 someI_ex)
qed

lemma DelProp_Part2:
  shows      "DelProperty (transformDel G1)"
proof-
  have 0: "\<And> G1. \<exists> G2. transformDelTest G1 G2"
    by (unfold transformDelTest_def, auto)
  from 0 have 1:  "\<exists> G2. transformDelTest G1 G2"
    by blast
  from 1 and DelProp_Part1 show ?thesis
    apply (unfold transformDel_def)
    by (smt (verit, ccfv_threshold) DelProp_Part1 someI_ex)
qed

lemma TermPreservesStart_Part1:
  assumes a: "StartProperty G1"
  assumes b: "transformTermTest G1 N G2"
  shows      "StartProperty G2"
proof-
  from a and b show ?thesis
    apply (unfold StartProperty_def transformTermTest_def NonTerminals_def NTInRule_def)
    using CollectI Diff_iff Un_iff empty_iff fst_conv insert_iff list.simps(15) by fastforce
qed

definition StartPropRel :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "StartPropRel G1 G2 \<equiv> (StartProperty G1 \<longrightarrow> StartProperty G2)"

lemma StartPropRel_rtrans: 
  shows "transp StartPropRel \<and> reflp StartPropRel"
proof-
  show ?thesis
    apply (unfold StartPropRel_def) 
    by (metis (mono_tags, lifting) reflpI transpI)
qed

lemma TermPreservesStart_Part2:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  assumes c: "StartProperty G1"
  shows      "StartProperty (transformTerm Gen G1)"
proof-
  have 0: "\<And> G1 N G2. transformTermTest G1 N G2 \<Longrightarrow> StartPropRel G1 G2"
    by (simp add: StartPropRel_def TermPreservesStart_Part1)
  from a b 0 have 1: "StartPropRel G1 (transformTerm Gen G1)"
    using TermTerminate_Part12 
    using StartPropRel_rtrans by blast
  from 1 and c show ?thesis 
    by (unfold StartPropRel_def, auto)
qed

lemma BinPreservesStart_Part1:
  assumes a: "StartProperty G1"
  assumes b: "transformBinTest G1 N G2"
  shows      "StartProperty G2"
proof-
  from a and b show ?thesis
    apply (unfold StartProperty_def transformBinTest_def NonTerminals_def NTInRule_def)
    using CollectI Diff_iff Un_iff empty_iff fst_conv insert_iff list.simps(15) by fastforce
qed

lemma BinPreservesStart_Part2:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  assumes c: "StartProperty G1"
  shows      "StartProperty (transformBin Gen G1)"
proof-
  have 0: "\<And> G1 N G2. transformBinTest G1 N G2 \<Longrightarrow> StartPropRel G1 G2"
    by (simp add: StartPropRel_def BinPreservesStart_Part1)
  from a b 0 have 1: "StartPropRel G1 (transformBin Gen G1)"
    using BinTerminate_Part12 
    using StartPropRel_rtrans by blast
  from 1 and c show ?thesis 
    by (unfold StartPropRel_def, auto)
qed

lemma DelPreservesStart_Part1:
  assumes a: "StartProperty G1"
  assumes b: "transformDelTest G1 G2"
  shows      "StartProperty G2"
proof-
  from b have 0: "\<And> R. R \<in> (snd G2) \<Longrightarrow> \<exists> R1. R1 \<in> (snd G1) \<and> set (snd R) \<subseteq> set (snd R1)"
    apply (unfold transformDelTest_def RemoveAllEpsilonProds_def DelAllNullableNTsFromRules_def DelNullableNTsFromRule_def)
    using DelFinite_Part3 apply (unfold RuleElementListSubset_def) 
    by fastforce
  from 0 and a show ?thesis
    apply (unfold StartProperty_def) 
    by (metis b fst_conv subset_code(1) transformDelTest_def) 
qed

lemma DelPreservesStart_Part2:
  assumes a: "StartProperty G1"
  shows      "StartProperty (transformDel G1)"
proof-
  have 0: "\<And> G1. \<exists> G2. transformDelTest G1 G2"
    by (unfold transformDelTest_def, auto)
  from 0 have 1:  "\<exists> G2. transformDelTest G1 G2"
    by blast
  from a and DelPreservesStart_Part1 show ?thesis 
    apply (unfold transformDel_def)
    by (smt (verit, best) "1" DelPreservesStart_Part1 someI_ex)
qed

lemma UnitPreservesStart_Part1:
  assumes a: "StartProperty G1"
  assumes b: "transformUnitTest G1 A G2"
  shows      "StartProperty G2"
proof-
  from b have 0: "\<And> R. R \<in> (snd G2) \<Longrightarrow> \<exists> R1. R1 \<in> (snd G1) \<and> (snd R) = (snd R1)"
    by (unfold transformUnitTest_def NewUnitTransRuleSet_def, auto)
  from 0 and a show ?thesis
    apply (unfold StartProperty_def)
    by (metis b fst_conv transformUnitTest_def)
qed

lemma UnitPreservesStart_Part2:
  assumes b: "finiteCFG G1"
  assumes c: "StartProperty G1"
  shows      "StartProperty (transformUnit G1)"
proof-
  have 0: "\<And> G1 N G2. transformUnitTest G1 N G2 \<Longrightarrow> StartPropRel G1 G2"
    by (simp add: StartPropRel_def UnitPreservesStart_Part1)
  from b 0 have 1: "StartPropRel G1 (transformUnit  G1)"
    using UnitTerminate_Part12 
    using StartPropRel_rtrans by blast
  from 1 and c show ?thesis 
    by (unfold StartPropRel_def, auto)
qed

definition TermPropRel :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "TermPropRel G1 G2 \<equiv> (TermProperty G1 \<longrightarrow> TermProperty G2)"

lemma TermPropRel_rtrans: 
  shows "transp TermPropRel \<and> reflp TermPropRel"
proof-
  show ?thesis
    apply (unfold TermPropRel_def) 
    by (metis (mono_tags, lifting) reflpI transpI)
qed

lemma BinPreservesTerm_Part1:
  assumes x: "TermProperty G1"
  assumes y: "transformBinTest G1 N G2"
  shows      "TermProperty G2"
proof-
  from y have 0: "\<exists> S R1 R2 R3 Rs1 Rs2 S1 L R a. 
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
    by (simp add: transformBinTest_def)
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
  from a and x and d and e have 1: "\<And> t. (T t) \<notin> set (L @ a # R)"
    apply (unfold TermProperty_def) 
    by (metis add_is_1 i length_0_conv length_Cons length_append list.distinct(1) snd_conv)
  from 1 have 2: "\<And> t. (T t) \<notin> set (a # R)" by auto
  from 1 have 3: "\<And> t. (T t) \<notin> set (L @ [NT N])" by auto
  from 1 and 2 and 3 and x show ?thesis
    apply (unfold TermProperty_def) 
    using r by auto
qed

lemma BinPreservesTerm_Part2:
  assumes a: "NewNTGen Gen"
  assumes b: "finiteCFG G1"
  assumes c: "TermProperty G1"
  shows      "TermProperty (transformBin Gen G1)"
proof-
  have 0: "\<And> G1 N G2. transformBinTest G1 N G2 \<Longrightarrow> TermPropRel G1 G2"
    by (simp add: TermPropRel_def BinPreservesTerm_Part1)
  from a b 0 have 1: "TermPropRel G1 (transformBin Gen G1)"
    using BinTerminate_Part12 
    using TermPropRel_rtrans by blast
  from 1 and c show ?thesis 
    by (unfold TermPropRel_def, auto)
qed

lemma DelPreservesTerm_Part1:
  assumes a: "TermProperty G1"
  assumes b: "transformDelTest G1 G2"
  shows      "TermProperty G2"
proof-
  from b have 0: "\<And> R. R \<in> (snd G2) \<Longrightarrow> \<exists> R1. R1 \<in> (snd G1) \<and> set (snd R) \<subseteq> set (snd R1) \<and> length (snd R) \<le> length (snd R1)"
    apply (unfold transformDelTest_def RemoveAllEpsilonProds_def DelAllNullableNTsFromRules_def DelNullableNTsFromRule_def)
    using DelFinite_Part3 DelFinite_Part6 apply (unfold RuleElementListSubset_def RuleElementListSize_def) 
    by fastforce
  from 0 and a show ?thesis
    apply (unfold TermProperty_def) 
    by (smt (verit, ccfv_threshold) add_Suc_shift add_eq_self_zero gr0_conv_Suc le_Suc_eq length_Cons 
        length_greater_0_conv length_pos_if_in_set less_le_not_le list.set_cases list.size(3) plus_nat.add_0 subset_eq)
qed

lemma DelPreservesTerm_Part2:
  assumes a: "TermProperty G1"
  shows      "TermProperty (transformDel G1)"
proof-
  have 0: "\<And> G1. \<exists> G2. transformDelTest G1 G2"
    by (unfold transformDelTest_def, auto)
  from 0 have 1:  "\<exists> G2. transformDelTest G1 G2"
    by blast
  from a and DelPreservesTerm_Part1 show ?thesis 
    apply (unfold transformDel_def)
    by (smt (verit, best) "1" DelPreservesTerm_Part1 someI_ex)
qed

lemma UnitPreservesTerm_Part1:
  assumes a: "TermProperty G1"
  assumes b: "transformUnitTest G1 A G2"
  shows      "TermProperty G2"
proof-
  from b have 0: "\<And> R. R \<in> (snd G2) \<Longrightarrow> \<exists> R1. R1 \<in> (snd G1) \<and> (snd R) = (snd R1)"
    by (unfold transformUnitTest_def NewUnitTransRuleSet_def, auto)
  from 0 and a show ?thesis
    apply (unfold TermProperty_def)
    by (metis)
qed

lemma UnitPreservesTerm_Part2:
  assumes b: "finiteCFG G1"
  assumes c: "TermProperty G1"
  shows      "TermProperty (transformUnit G1)"
proof-
  have 0: "\<And> G1 N G2. transformUnitTest G1 N G2 \<Longrightarrow> TermPropRel G1 G2"
    by (simp add: TermPropRel_def UnitPreservesTerm_Part1)
  from b 0 have 1: "TermPropRel G1 (transformUnit  G1)"
    using UnitTerminate_Part12 
    using TermPropRel_rtrans by blast
  from 1 and c show ?thesis 
    by (unfold TermPropRel_def, auto)
qed

definition BinPropRel :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "BinPropRel G1 G2 \<equiv> (BinProperty G1 \<longrightarrow> BinProperty G2)"

lemma BinPropRel_rtrans: 
  shows "transp BinPropRel \<and> reflp BinPropRel"
proof-
  show ?thesis
    apply (unfold BinPropRel_def) 
    by (metis (mono_tags, lifting) reflpI transpI)
qed

lemma DelPreservesBin_Part1:
  assumes a: "BinProperty G1"
  assumes b: "transformDelTest G1 G2"
  shows      "BinProperty G2"
proof-
  from b have 0: "\<And> R. R \<in> (snd G2) \<Longrightarrow> \<exists> R1. R1 \<in> (snd G1) \<and>  length (snd R) \<le> length (snd R1)"
    apply (unfold transformDelTest_def RemoveAllEpsilonProds_def DelAllNullableNTsFromRules_def DelNullableNTsFromRule_def)
    using DelFinite_Part6 apply (unfold RuleElementListSize_def) 
    by fastforce
  from 0 and a show ?thesis
    apply (unfold BinProperty_def) 
    using dual_order.trans by blast
qed

lemma DelPreservesBin_Part2:
  assumes a: "BinProperty G1"
  shows      "BinProperty (transformDel G1)"
proof-
  have 0: "\<And> G1. \<exists> G2. transformDelTest G1 G2"
    by (unfold transformDelTest_def, auto)
  from 0 have 1:  "\<exists> G2. transformDelTest G1 G2"
    by blast
  from a and DelPreservesBin_Part1 show ?thesis 
    apply (unfold transformDel_def)
    by (smt (verit, best) "1" DelPreservesBin_Part1 someI_ex)
qed

lemma UnitPreservesBin_Part1:
  assumes a: "BinProperty G1"
  assumes b: "transformUnitTest G1 A G2"
  shows      "BinProperty G2"
proof-
  from b have 0: "\<And> R. R \<in> (snd G2) \<Longrightarrow> \<exists> R1. R1 \<in> (snd G1) \<and> (snd R) = (snd R1)"
    by (unfold transformUnitTest_def NewUnitTransRuleSet_def, auto)
  from 0 and a show ?thesis
    apply (unfold BinProperty_def)
    by (metis)
qed

lemma UnitPreservesBin_Part2:
  assumes b: "finiteCFG G1"
  assumes c: "BinProperty G1"
  shows      "BinProperty (transformUnit G1)"
proof-
  have 0: "\<And> G1 N G2. transformUnitTest G1 N G2 \<Longrightarrow> BinPropRel G1 G2"
    by (simp add: BinPropRel_def UnitPreservesBin_Part1)
  from b 0 have 1: "BinPropRel G1 (transformUnit  G1)"
    using UnitTerminate_Part12 
    using BinPropRel_rtrans by blast
  from 1 and c show ?thesis 
    by (unfold BinPropRel_def, auto)
qed

definition DelStartPropRel :: "('n, 't) CFG \<Rightarrow> ('n, 't) CFG \<Rightarrow> bool"
  where "DelStartPropRel G1 G2 \<equiv> (DelProperty G1 \<and> StartProperty G1 \<longrightarrow> DelProperty G2 \<and> StartProperty G2)"

lemma DelStartPropRel_rtrans: 
  shows "transp DelStartPropRel \<and> reflp DelStartPropRel"
proof-
  show ?thesis
    apply (unfold DelStartPropRel_def) 
    by (metis (mono_tags, lifting) reflpI transpI)
qed

lemma UnitPreservesDelStart_Part1:
  assumes x: "DelProperty G1"
  assumes y: "StartProperty G1"
  assumes z: "transformUnitTest G1 N G2"
  shows      "DelProperty G2"
proof-
  show ?thesis
  proof (rule ccontr)
    assume contr: "\<not> DelProperty G2"
    from z have 0: "\<exists> S Rs1 Rs2. 
                  (S, Rs1) = G1
                  \<and> (S, Rs2) = G2
                  \<and> HasUnitProductionRule Rs1 N
                  \<and> Rs2 = (Rs1 \<union> (NewUnitTransRuleSet N Rs1)) - (NTToNTSetForA N)"
          (is "\<exists> S Rs1 Rs2. ?P S Rs1 Rs2")
    by (simp add: transformUnitTest_def)
    then obtain S Rs1 Rs2 where r: "?P S Rs1 Rs2" by blast
    from r have a: "G1 = (S, Rs1)" by auto
    from r have b: "G2 = (S, Rs2)" by auto
    from r have c: "HasUnitProductionRule Rs1 N" by auto
    from r have d: "Rs2 = (Rs1 \<union> (NewUnitTransRuleSet N Rs1)) - (NTToNTSetForA N)" by auto
    from contr have 1: "\<exists> A. (A, []) \<in> Rs2 \<and> A \<noteq> S" (is "\<exists> A. ?P A")
      by (simp add: DelProperty_def b)
    then obtain A where 2: "?P A" by blast
    from d and a and x and 2 have 3: "(A, []) \<in> (NewUnitTransRuleSet N Rs1)" 
      by (metis "2" DelProperty_def DiffD1 Un_iff fst_conv snd_conv)
    from 3 have 4: "\<exists> B. (N, B) \<in>  NTToNTProductionSet Rs1 \<and> (B, []) \<in> Rs1" (is "\<exists> B. ?P B")
      by (unfold NewUnitTransRuleSet_def, auto)
    then obtain B where 5: "?P B" by blast
    from 5 and x and a have 6: "B = S" 
      by (simp add: DelProperty_def, auto)
    from 6 and 5 have 7: "(N, S) \<in> NTToNTProductionSet Rs1"
      by auto
    from 7 and y and a show "False"
      apply (unfold StartProperty_def NTToNTProductionSet_def, simp) 
      by (metis (mono_tags, lifting) CollectD list.set_intros(1) old.prod.case tranclE)
  qed
qed

lemma UnitPreservesDelStart_Part2:
  assumes x: "DelProperty G1"
  assumes y: "StartProperty G1"
  assumes z: "transformUnitTest G1 N G2"
  shows      "DelProperty G2 \<and> StartProperty G2"
proof-
  show ?thesis 
    by (meson UnitPreservesDelStart_Part1 UnitPreservesStart_Part1 x y z)
qed

lemma UnitPreservesDelStart_Part3:
  assumes a: "finiteCFG G1"
  assumes b: "DelProperty G1"
  assumes c: "StartProperty G1"
  shows      "DelProperty (transformUnit G1) \<and> StartProperty (transformUnit G1)"
proof-
  have 0: "\<And> G1 N G2. transformUnitTest G1 N G2 \<Longrightarrow> DelStartPropRel G1 G2"
    apply (simp add: DelStartPropRel_def UnitPreservesBin_Part2) 
    by (meson UnitPreservesDelStart_Part1 UnitPreservesStart_Part1)
  from 0 have 1: "DelStartPropRel G1 (transformUnit  G1)"
    using UnitTerminate_Part12 
    using DelStartPropRel_rtrans a by blast
  from 1 and c and b show ?thesis 
    by (unfold DelStartPropRel_def, auto)
qed















