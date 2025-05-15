section \<open>Total Correctness\<close>

text \<open>This theory formalises total correctness as a Hoare style triple over big step semantics.
      A program $c$ is said to terminate for state $\sigma$ if $c \downarrow s$.\<close>

theory Total_Correctness
  imports Correctness
begin

locale total_correctness = correctness +
  fixes terminates :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infixl \<open>\<down>\<close> 50)
begin

subsection \<open>Defining Total Correctness\<close>

text \<open>Total correctness is defined informally as $partial correctness + termination$.\<close>

definition
  thoare :: \<open>'b assn \<Rightarrow> 'a \<Rightarrow> 'b assn \<Rightarrow> bool\<close> (\<open>\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_)}\<close> 50) 
where
  \<open>\<Turnstile>\<^sub>t {P}c{Q} \<longleftrightarrow> (\<Turnstile> {P}c{Q} \<and> (\<forall>s. P s \<longrightarrow> c \<down> s))\<close>

lemma thoare_alt_def: \<open>\<Turnstile>\<^sub>t {P}c{Q} \<longleftrightarrow> ((\<forall>s t. P s \<longrightarrow> c \<down> s \<and> ((c, s) \<Rightarrow> t \<longrightarrow> Q t)))\<close>
  unfolding thoare_def hoare_def by auto

text \<open>Thus, from it's definition, total correctness implies partial correctness.\<close>

lemma thoare_imp_hoareI:
  assumes \<open>\<Turnstile>\<^sub>t {P}c{Q}\<close>
    shows \<open>\<Turnstile> {P}c{Q}\<close> 
  using assms unfolding thoare_def by (elim conjE)

lemma thoare_is_term_hoare:
    shows \<open>\<Turnstile>\<^sub>t {P}c{Q} \<longleftrightarrow> \<Turnstile>\<^sub>t {P}c{\<lambda>_. True} \<and> \<Turnstile> {P}c{Q}\<close> 
  unfolding thoare_def by auto

subsection \<open>Rules of Total Correctness\<close>

subsubsection \<open>False Precondition\<close>

lemma thoare_pre_false_impI: 
  assumes \<open>\<And>s. P s \<Longrightarrow> False\<close>
    shows \<open>\<Turnstile>\<^sub>t {P}c{Q}\<close>
  unfolding thoare_def apply (intro conjI hoare_pre_false_impI)
  using assms by auto

lemma thoare_pre_false[simp]: \<open>\<Turnstile>\<^sub>t {\<lambda>_. False}c{Q}\<close>
  by (rule thoare_pre_false_impI)

subsubsection \<open>Excluded Miracle\<close>

lemma thoare_excluded_miracleI(*[intro!]*): 
  assumes \<open>\<And>s. \<not> P s\<close>
  shows \<open>\<Turnstile>\<^sub>t {P}c{\<lambda>_. False}\<close>
  unfolding thoare_def apply (intro conjI hoare_excluded_miracleI)
  using assms by auto

subsubsection \<open>Termination\<close>

lemma thoare_termination(*[intro!]*):
  assumes \<open>\<And>s. P s \<Longrightarrow> c \<down> s\<close>
    shows \<open>\<Turnstile>\<^sub>t {P}c{\<lambda>_. True}\<close>
  unfolding thoare_def using assms by auto

subsubsection \<open>Precondition Strengthening\<close>

lemma thoare_pre_strengthI: 
  assumes thoare: \<open>\<Turnstile>\<^sub>t {P}c{Q}\<close> and strengthen: \<open>\<And>s. P' s \<Longrightarrow> P s\<close> 
    shows \<open>\<Turnstile>\<^sub>t {P'}c{Q}\<close>
  using thoare unfolding thoare_def apply safe
  subgoal by (rule hoare_pre_strengthI[OF _ strengthen])
  subgoal for s apply (erule allE[where x = s])
    using strengthen by auto
  .

subsubsection \<open>Postcondition Weakening\<close>

lemma thoare_post_weakI: 
  assumes thoare: \<open>\<Turnstile>\<^sub>t {P}c{Q}\<close> and weaken: \<open>\<And>s. Q s \<Longrightarrow> Q' s\<close> 
    shows \<open>\<Turnstile>\<^sub>t {P}c{Q'}\<close>
  using thoare unfolding thoare_def apply safe
  subgoal by (rule hoare_post_weakI[OF _ weaken])
  .

subsubsection \<open>Postcondition Conjunctivity\<close>

lemma thoare_post_conjI[intro!]:
  assumes \<open>\<Turnstile>\<^sub>t {P} c {Q\<^sub>1}\<close> and \<open>\<Turnstile>\<^sub>t {P} c {Q\<^sub>2}\<close>
    shows \<open>\<Turnstile>\<^sub>t {P} c {\<lambda>s. Q\<^sub>1 s \<and> Q\<^sub>2 s}\<close>
  using assms unfolding thoare_def by clarify

lemma thoare_post_conjE[elim!]:
  assumes major: \<open>\<Turnstile>\<^sub>t {P} c {\<lambda>s. Q\<^sub>1 s \<and> Q\<^sub>2 s}\<close>
      and minor: \<open>\<lbrakk>\<Turnstile>\<^sub>t {P} c {Q\<^sub>1}; \<Turnstile>\<^sub>t {P} c {Q\<^sub>2}\<rbrakk> \<Longrightarrow> R\<close>
    shows R
  by (rule minor; rule thoare_post_weakI[OF major], elim conjE)

lemma thoare_post_conj[simp]: \<open>\<Turnstile>\<^sub>t {P} c {\<lambda>s. Q\<^sub>1 s \<and> Q\<^sub>2 s} \<equiv> \<Turnstile>\<^sub>t {P} c {Q\<^sub>1} \<and> \<Turnstile>\<^sub>t {P} c {Q\<^sub>2}\<close>
  unfolding atomize_eq by safe

subsubsection \<open>Precondition Disjunctivity\<close>

lemma thoare_pre_disjI[intro!]:
  assumes \<open>\<Turnstile>\<^sub>t {P\<^sub>1} c {Q}\<close> and \<open>\<Turnstile>\<^sub>t {P\<^sub>2} c {Q}\<close>
    shows \<open>\<Turnstile>\<^sub>t {\<lambda>s. P\<^sub>1 s \<or> P\<^sub>2 s} c {Q}\<close>
  using assms unfolding thoare_def apply safe
  by auto

lemma thoare_pre_disjE[elim!]:
  assumes major: \<open>\<Turnstile>\<^sub>t {\<lambda>s. P\<^sub>1 s \<or> P\<^sub>2 s} c {Q}\<close>
      and minor: \<open>\<lbrakk>\<Turnstile>\<^sub>t {P\<^sub>1} c {Q}; \<Turnstile>\<^sub>t {P\<^sub>2} c {Q}\<rbrakk> \<Longrightarrow> R\<close>
    shows R
  apply (rule minor; rule thoare_pre_strengthI[OF major])
  subgoal by (rule disjI1) 
  subgoal by (rule disjI2)
  .

lemma thoare_pre_disj[simp]: \<open>\<Turnstile>\<^sub>t {\<lambda>s. P\<^sub>1 s \<or> P\<^sub>2 s} c {Q} \<equiv> (\<Turnstile>\<^sub>t {P\<^sub>1} c {Q} \<and> \<Turnstile>\<^sub>t {P\<^sub>2} c {Q})\<close>
  unfolding atomize_eq by safe

subsubsection \<open>Postcondition Conjunctivity\<close>

lemma thoare_post_disjI(*[intro!]*):
  assumes \<open>\<Turnstile>\<^sub>t {P} c {Q\<^sub>1} \<or> \<Turnstile>\<^sub>t {P} c {Q\<^sub>2}\<close>
    shows \<open>\<Turnstile>\<^sub>t {P} c {\<lambda>s. Q\<^sub>1 s \<or> Q\<^sub>2 s}\<close>
  using assms apply (elim disjE)
  subgoal by (rule thoare_post_weakI, assumption, rule disjI1)
  subgoal by (rule thoare_post_weakI, assumption, rule disjI2)
  .

end

end
