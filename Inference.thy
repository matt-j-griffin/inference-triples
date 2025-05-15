theory Inference
  imports Correctness Incorrectness
begin

locale inference = correctness big_step + incorrectness big_step
  for big_step :: \<open>('prog \<times> 'state) \<Rightarrow> 'state \<Rightarrow> bool\<close> (infix \<open>\<Rightarrow>\<close> 55)
begin

text \<open>Principle of Agreement\<close>

lemma agreement: 
  assumes \<open>\<Turnstile> [P] c [Q]\<close> and \<open>\<And>s. P s \<Longrightarrow> P' s\<close>
      and \<open>\<Turnstile> {P'} c {Q'}\<close>
      and \<open>Q t\<close>
    shows \<open>Q' t\<close>
  apply (insert assms(1,3-)) 
  unfolding ohearn_def hoare_def
  apply (erule allE[where x = t], elim impE exE conjE)
  apply assumption
  subgoal for s
    apply (erule allE[where x = s], erule allE[where x = t], elim impE exE conjE)
    defer
    by (rule assms(2))
  .

text \<open>Principle of Denial\<close>

lemma denial:
  assumes ohearn: \<open>\<Turnstile> [P] c [Q]\<close> and P: \<open>\<And>s. P s \<Longrightarrow> P' s\<close>
      and Q: \<open>\<not>(\<forall>t. Q t \<longrightarrow> Q' t)\<close>
    shows \<open>\<not>\<Turnstile> {P'} c {Q'}\<close>
  using ohearn Q apply (intro notI)
  unfolding ohearn_def hoare_def apply clarify
  subgoal for t
    apply (erule allE[where x = t], elim impE exE conjE)
    apply assumption
    subgoal for s
      apply (erule allE[where x = s], elim allE[where x = t] impE exE conjE)
      defer
      by (rule P)
    .
  .


end

end
