section \<open>Correctness\<close>

text \<open>This theory formalises partial correctness as a Hoare style triple over big step semantics.\<close>

theory Correctness
  imports HOL.Product_Type
begin

type_synonym 'state assn = \<open>'state \<Rightarrow> bool\<close>

locale correctness =
  fixes big_step :: \<open>('prog \<times> 'state) \<Rightarrow> 'state \<Rightarrow> bool\<close> (infix \<open>\<Rightarrow>\<close> 55)
begin

subsection \<open>Defining Correctness\<close>

text \<open>A Hoare triple defines partial correctness of a command $c$ over a pre-state $\sigma$ 
      satisfying the predicate $P$, resulting in a post-state $\tau$ satisfying the predicate $Q$. 
      In the locale, we assume the existence of a big-step transition relation 
      $(c, \sigma) \Rightarrow \tau$ defining the execution of $c$ from state $\sigma$ to
      termination, resulting in state $\tau$.
      Thus, we have the well-known under- and over-approximating rule:.\<close>


definition
  hoare :: \<open>'state assn \<Rightarrow> 'prog \<Rightarrow> 'state assn \<Rightarrow> bool\<close> (\<open>\<Turnstile> {(1_)}/ (_)/ {(1_)}\<close> 50) 
where
  \<open>\<Turnstile> {P}c{Q} \<longleftrightarrow> (\<forall>s t. (c, s) \<Rightarrow> t \<longrightarrow> P s \<longrightarrow> Q t)\<close>

subsection \<open>Rules of Correctness\<close>

subsubsection \<open>False Precondition\<close>

lemma hoare_pre_false_impI: 
  assumes \<open>\<And>s. P s \<Longrightarrow> False\<close>
    shows \<open>\<Turnstile> {P}c{Q}\<close>
  unfolding hoare_def apply (intro allI impI)
  apply (drule assms(1))
  by blast

lemma hoare_pre_false[simp]: \<open>\<Turnstile> {\<lambda>_. False}c{Q}\<close>
  by (rule hoare_pre_false_impI)

subsubsection \<open>Excluded Miracle\<close>

lemma hoare_excluded_miracleI(*[intro!]*): 
  assumes \<open>\<And>s. \<not> P s\<close>
    shows \<open>\<Turnstile> {P}c{\<lambda>_. False}\<close>
unfolding hoare_def proof clarify
  fix s assume \<open>P s\<close> thus False
    using assms[of s] by (elim notE)
qed

subsubsection \<open>Termination\<close>

lemma hoare_termination[simp]: \<open>\<Turnstile> {P}c{\<lambda>_. True}\<close>
  unfolding hoare_def by auto

subsubsection \<open>Precondition Strengthening\<close>

lemma hoare_pre_strengthI: 
  assumes hoare: \<open>\<Turnstile> {P}c{Q}\<close> and strengthen: \<open>\<And>s. P' s \<Longrightarrow> P s\<close>
    shows \<open>\<Turnstile> {P'}c{Q}\<close>
using hoare unfolding hoare_def proof clarify
  fix s t assume major: \<open>\<forall>s t. (c, s) \<Rightarrow> t \<longrightarrow> P s \<longrightarrow> Q t\<close> and exec: \<open>(c, s) \<Rightarrow> t\<close> and pre: \<open>P' s\<close> 
  have P_implies_Q: \<open>P s \<Longrightarrow> Q t\<close> 
    by (insert major exec, erule allE[where x = s], elim allE[where x = t] impE)
  show \<open>Q t\<close>
    by (intro pre strengthen P_implies_Q)
qed

subsubsection \<open>Postcondition Weakening\<close>

lemma hoare_post_weakI:
  assumes hoare: \<open>\<Turnstile> {P}c{Q}\<close> and weaken: \<open>\<And>s. Q s \<Longrightarrow> Q' s\<close> 
    shows \<open>\<Turnstile> {P}c{Q'}\<close>
using hoare unfolding hoare_def proof clarify
  fix s t assume \<open>\<forall>s t. (c, s) \<Rightarrow> t \<longrightarrow> P s \<longrightarrow> Q t\<close> \<open>(c, s) \<Rightarrow> t\<close> \<open>P s\<close> 
  hence \<open>Q t\<close>
    by - (erule allE[where x = s], elim allE[where x = t] impE)
  thus \<open>Q' t\<close>
    by (rule weaken)
qed

subsubsection \<open>Postcondition Conjunctivity\<close>

lemma hoare_post_conjI[intro!]:
  assumes \<open>\<Turnstile> {P} c {Q\<^sub>1}\<close> and \<open>\<Turnstile> {P} c {Q\<^sub>2}\<close>
    shows \<open>\<Turnstile> {P} c {\<lambda>s. Q\<^sub>1 s \<and> Q\<^sub>2 s}\<close>
using assms unfolding hoare_def proof clarify
  fix s t assume major1: \<open>\<forall>s t. (c, s) \<Rightarrow> t \<longrightarrow> P s \<longrightarrow> Q\<^sub>1 t\<close> 
    and major2: \<open>\<forall>s t. (c, s) \<Rightarrow> t \<longrightarrow> P s \<longrightarrow> Q\<^sub>2 t\<close> 
    and prems: \<open>(c, s) \<Rightarrow> t\<close> \<open>P s\<close> 
  have \<open>Q\<^sub>1 t\<close> 
    using major1 prems by - (erule allE[where x = s], elim allE[where x = t] impE)
  moreover have \<open>Q\<^sub>2 t\<close>
    using major2 prems by - (erule allE[where x = s], elim allE[where x = t] impE)
  ultimately show \<open>Q\<^sub>1 t \<and> Q\<^sub>2 t\<close>
    by (intro conjI)
qed

lemma hoare_post_conjE[elim!]:
  assumes major: \<open>\<Turnstile> {P} c {\<lambda>s. Q\<^sub>1 s \<and> Q\<^sub>2 s}\<close>
      and minor: \<open>\<lbrakk>\<Turnstile> {P} c {Q\<^sub>1}; \<Turnstile> {P} c {Q\<^sub>2}\<rbrakk> \<Longrightarrow> R\<close>
    shows R
  by (rule minor; rule hoare_post_weakI[OF major], elim conjE)

lemma hoare_post_conj[simp]: \<open>\<Turnstile> {P} c {\<lambda>s. Q\<^sub>1 s \<and> Q\<^sub>2 s} \<equiv> \<Turnstile> {P} c {Q\<^sub>1} \<and> \<Turnstile> {P} c {Q\<^sub>2}\<close>
  unfolding atomize_eq by safe

subsubsection \<open>Precondition Disjunctivity\<close>

lemma hoare_pre_disjI[intro!]:
  assumes \<open>\<Turnstile> {P\<^sub>1} c {Q}\<close> and \<open>\<Turnstile> {P\<^sub>2} c {Q}\<close>
    shows \<open>\<Turnstile> {\<lambda>s. P\<^sub>1 s \<or> P\<^sub>2 s} c {Q}\<close>
  unfolding hoare_def
  apply (intro allI impI)
  subgoal for s t
    apply (elim disjE)
    subgoal
      using assms(1) unfolding hoare_def apply -
      by (erule allE[where x = s], erule allE[where x = t], elim impE)
    subgoal
      using assms(2) unfolding hoare_def apply -
      by (erule allE[where x = s], erule allE[where x = t], elim impE)
    .
  .

lemma hoare_pre_disjE[elim!]:
  assumes major: \<open>\<Turnstile> {\<lambda>s. P\<^sub>1 s \<or> P\<^sub>2 s} c {Q}\<close>
      and minor: \<open>\<lbrakk>\<Turnstile> {P\<^sub>1} c {Q}; \<Turnstile> {P\<^sub>2} c {Q}\<rbrakk> \<Longrightarrow> R\<close>
    shows R
  apply (rule minor; rule hoare_pre_strengthI[OF major])
  subgoal by (rule disjI1) 
  subgoal by (rule disjI2)
  .

lemma hoare_pre_disj[simp]: \<open>\<Turnstile> {\<lambda>s. P\<^sub>1 s \<or> P\<^sub>2 s} c {Q} \<equiv> (\<Turnstile> {P\<^sub>1} c {Q} \<and> \<Turnstile> {P\<^sub>2} c {Q})\<close>
  unfolding atomize_eq by safe

subsubsection \<open>Postcondition Disjunctivity\<close>

lemma hoare_post_disjI(*[intro!]*):
  assumes \<open>\<Turnstile> {P} c {Q\<^sub>1} \<or> \<Turnstile> {P} c {Q\<^sub>2}\<close>
    shows \<open>\<Turnstile> {P} c {\<lambda>s. Q\<^sub>1 s \<or> Q\<^sub>2 s}\<close>
  using assms apply (rule disjE)
  subgoal by (rule hoare_post_weakI, assumption, rule disjI1)
  subgoal by (rule hoare_post_weakI, assumption, rule disjI2)
  .

end

end
