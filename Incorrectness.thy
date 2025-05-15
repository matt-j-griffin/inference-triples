section \<open>Incorrectness\<close>

text \<open>This theory formalises incorrectness as a Hoare style triple over big step semantics.\<close>

theory Incorrectness
  imports HOL.Product_Type
begin

type_synonym 'state assn = \<open>'state \<Rightarrow> bool\<close>

text \<open>Proofs of incorrectness often require non-triviality.\<close>

definition
  nontrivial :: \<open>('state \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>nontrivial Q \<equiv> (\<exists>t. Q t)\<close>

locale incorrectness =
  fixes big_step :: \<open>('prog \<times> 'state) \<Rightarrow> 'state \<Rightarrow> bool\<close> (infix \<open>\<Rightarrow>\<close> 55)
begin

subsection \<open>Defining Incorrectness\<close>

definition 
  ohearn :: \<open>'state assn \<Rightarrow> 'prog \<Rightarrow> 'state assn \<Rightarrow> bool\<close> (\<open>\<Turnstile> [(1_)]/ (_)/ [(1_)]\<close> 50) 
where
  \<open>\<Turnstile> [P] c [Q] = (\<forall>t. Q t \<longrightarrow> (\<exists>s. P s \<and> (c, s) \<Rightarrow> t))\<close>

subsection \<open>Rules of Incorrectness\<close>

subsubsection \<open>False Postcondition\<close>

lemma ohearn_imp_false_postI(*[intro!]*): 
  assumes \<open>\<And>s. Q s \<Longrightarrow> False\<close>
    shows \<open>\<Turnstile> [P] c [Q]\<close>
  unfolding ohearn_def apply (intro allI impI)
  using assms by auto

lemma ohearn_false_post[simp]: \<open>\<Turnstile> [P] c [\<lambda>_. False]\<close>
  by (rule ohearn_imp_false_postI)

subsubsection \<open>Excluded Miracle\<close>

lemma ohearn_excluded_miracleI(*[intro!]*): 
  assumes \<open>\<And>s. \<not> Q s\<close>
    shows \<open>\<Turnstile> [\<lambda>_. False] c [Q]\<close>
unfolding ohearn_def proof (intro iffI allI impI)
  fix t assume \<open>Q t\<close> thus \<open>\<exists>s. False \<and> (c, s) \<Rightarrow> t\<close>
    using assms[of t] by (elim notE)
qed

subsubsection \<open>Precondition Weakening\<close>

lemma ohearn_pre_weakI:
  assumes \<open>\<Turnstile> [P] c [Q]\<close> and impP: \<open>\<And>s. P s \<Longrightarrow> P' s\<close>
    shows \<open>\<Turnstile> [P'] c [Q]\<close>
  using assms(1) unfolding ohearn_def apply (intro allI impI)
  subgoal for t
    apply (erule allE[of _ t], elim impE, assumption)
    subgoal
      apply (elim exE conjE)
      subgoal for s
        apply (rule exI[of _ s], intro conjI)
        subgoal by (rule impP)
        subgoal .
        .
      .
    .
  .

subsubsection \<open>Postcondition Strengthening\<close>

lemma ohearn_post_strengthI:
  assumes ohearn: \<open>\<Turnstile> [P] c [Q]\<close> and strength: \<open>\<And>s. Q' s \<Longrightarrow> Q s\<close>
    shows \<open>\<Turnstile> [P] c [Q']\<close>
  using ohearn unfolding ohearn_def apply (intro allI impI)
  subgoal for t
    apply (erule allE[of _ t], elim impE)
    subgoal by (rule strength)
    subgoal
      apply (elim exE conjE)
      subgoal for s
        by (rule exI[of _ s], intro conjI)
      .
    .
  .

subsubsection \<open>Precondition Conjunctivity\<close>

lemma ohearn_pre_conjE(*[intro!]*):
  assumes major: \<open>\<Turnstile> [\<lambda>s. P\<^sub>1 s \<and> P\<^sub>2 s] c [Q]\<close>
      and minor: \<open>\<lbrakk>\<Turnstile> [P\<^sub>1] c [Q]; \<Turnstile> [P\<^sub>2] c [Q]\<rbrakk> \<Longrightarrow> R\<close>
    shows R
  by (intro minor ohearn_pre_weakI[OF major]; elim conjE)

subsubsection \<open>Precondition Disjunctivity\<close>

lemma ohearn_pre_disjI(*[intro!]*):
  assumes \<open>\<Turnstile> [P\<^sub>1] c [Q] \<or> \<Turnstile> [P\<^sub>2] c [Q]\<close>
    shows \<open>\<Turnstile> [\<lambda>s. P\<^sub>1 s \<or> P\<^sub>2 s] c [Q]\<close>
  using assms unfolding ohearn_def apply (intro allI impI)
  subgoal for t
    apply (elim allE[of _ t] disjE impE exE conjE)
    apply assumption
    subgoal for s
      by (intro conjI disjI1 exI[of _ s])
    apply assumption
    subgoal for s
      by (intro conjI disjI2 exI[of _ s])
    .
  .

subsubsection \<open>Postcondition Conjunctivity\<close>

lemma ohearn_post_conjI(*[intro!]*):
  assumes \<open>\<Turnstile> [P] c [Q\<^sub>1] \<or> \<Turnstile> [P] c [Q\<^sub>2]\<close>
    shows \<open>\<Turnstile> [P] c [\<lambda>s. Q\<^sub>1 s \<and> Q\<^sub>2 s]\<close>
  using assms unfolding ohearn_def apply (intro allI impI)
  subgoal for t
    by (elim disjE conjE allE[of _ t] impE, assumption+)
  . 

subsubsection \<open>Postcondition Disjunctivity\<close>

lemma ohearn_post_disjI(*[intro!]*):
  assumes \<open>\<Turnstile> [P] c [Q\<^sub>1]\<close> and \<open>\<Turnstile> [P] c [Q\<^sub>2]\<close>
    shows \<open>\<Turnstile> [P] c [\<lambda>t. Q\<^sub>1 t \<or> Q\<^sub>2 t]\<close>
  unfolding ohearn_def apply (intro allI impI)
  subgoal for t
    apply (elim disjE)
    subgoal
      using assms(1) unfolding ohearn_def by (elim allE[of _ t] impE)
    subgoal
      using assms(2) unfolding ohearn_def by (elim allE[of _ t] impE)
    .
  .

lemma ohearn_post_disjE(*(*[elim!]*)*):
  assumes major: \<open>\<Turnstile> [P] c [\<lambda>t. Q\<^sub>1 t \<or> Q\<^sub>2 t]\<close>
      and minor: \<open>\<lbrakk>\<Turnstile> [P] c [Q\<^sub>1]; \<Turnstile> [P] c [Q\<^sub>2]\<rbrakk> \<Longrightarrow> R\<close>
    shows R
  by (intro minor ohearn_post_strengthI[OF major], safe)

lemma ohearn_post_disj[simp]: \<open>\<Turnstile> [P] c [\<lambda>t. Q\<^sub>1 t \<or> Q\<^sub>2 t] \<longleftrightarrow> (\<Turnstile> [P] c [Q\<^sub>1] \<and> \<Turnstile> [P] c [Q\<^sub>2])\<close>
  by (intro iffI ohearn_post_disjI conjI; elim ohearn_post_disjE conjE)

end

end
