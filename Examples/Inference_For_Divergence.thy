theory Inference_For_Divergence                                                       
  imports "Abstract-Triples.Total_Inference" 
          HoareForDivergence.StdLogic 
          HoareForDivergence.WhileLangLemmas 
begin

text \<open>Instantiate total (In)correctness inferences for divergence logic.\<close>

interpretation total_inference \<open>\<lambda>c s. Ex (terminates s c)\<close> \<open>\<lambda>(c,s). exec s c\<close>
  .

lemma \<open>hoare_sem P c Q \<longleftrightarrow> thoare P c Q\<close>
unfolding hoare_sem_def thoare_alt_def prod.case terminates_eq_exec[symmetric] all_simps
proof (intro iffI allI impI conjI)
  fix s assume \<open>\<forall>s. P s \<longrightarrow> (\<exists>t. terminates s c t \<and> Q t)\<close> \<open>P s\<close>
  thus \<open>Ex (terminates s c)\<close>
  proof (elim allE[where x = s] impE exE conjE) 
    fix t assume termi: \<open>terminates s c t\<close> and \<open>P s\<close> \<open>Q t\<close> 
    show \<open>Ex (terminates s c)\<close>
      by (intro exI[where x = t] termi)
  qed
next
  fix s t assume \<open>\<forall>s. P s \<longrightarrow> (\<exists>t. terminates s c t \<and> Q t)\<close> \<open>P s\<close> and exec: \<open>terminates s c t\<close>
  thus \<open>Q t\<close>
  proof (elim allE[where x = s] impE exE conjE)
    fix t' assume termi: \<open>terminates s c t'\<close> and \<open>P s\<close> \<open>Q t'\<close> 
    thus \<open>Q t\<close>
      using exec unfolding terminates_eq_exec[symmetric]
      using terminates_deterministic by blast
  qed
next
  fix s assume \<open>\<forall>s. P s \<longrightarrow> Ex (terminates s c) \<and> (\<forall>t. terminates s c t \<longrightarrow> Q t)\<close> \<open>P s\<close> 
  thus \<open>\<exists>t. terminates s c t \<and> Q t\<close>
  proof (elim allE[where x = s] impE)
    assume \<open>Ex (terminates s c) \<and> (\<forall>t. terminates s c t \<longrightarrow> Q t)\<close>
      thus \<open>\<exists>t. terminates s c t \<and> Q t\<close>
    proof (elim exE conjE)
      fix t assume \<open>\<forall>t. terminates s c t \<longrightarrow> Q t\<close> \<open>terminates s c t\<close>
      thus \<open>\<exists>t. terminates s c t \<and> Q t\<close>
      proof (elim allE[where x = t] impE)
        assume \<open>terminates s c t\<close> \<open>Q t\<close> thus \<open>\<exists>t. terminates s c t \<and> Q t\<close>
          by (intro conjI exI[where x = t])
      qed
    qed
  qed
qed

end
