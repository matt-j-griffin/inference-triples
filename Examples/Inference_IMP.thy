theory Inference_IMP
  imports "Abstract-Triples.Total_Inference" 
          "HOL-IMP.Hoare_Total"
          "Relational-Incorrectness-Logic.RelationalIncorrectness"
begin

text \<open>Instantiate (In)correctness inferences for HOL-IMP.\<close>

interpretation i: total_inference \<open>\<lambda>c s. \<exists>t. (c, s) \<Rightarrow> t\<close> big_step
  .

text \<open>Hoare IMP is equivalent to correctness formalisation.\<close>

lemma \<open>hoare_valid P c Q \<longleftrightarrow> i.hoare P c Q\<close>
  unfolding hoare_valid_def i.hoare_def by auto

lemma \<open>hoare_tvalid P c Q \<longleftrightarrow> i.thoare P c Q\<close>
unfolding hoare_tvalid_def i.thoare_alt_def proof safe
  fix s t assume \<open>\<forall>s. P s \<longrightarrow> (\<exists>t. (c, s) \<Rightarrow> t \<and> Q t)\<close> \<open>P s\<close> \<open>(c, s) \<Rightarrow> t\<close> 
  thus \<open>Q t\<close>
  proof (elim allE[where x = s] impE exE conjE)
    fix t' assume prems: \<open>(c, s) \<Rightarrow> t\<close> \<open>(c, s) \<Rightarrow> t'\<close> and Q: \<open>Q t'\<close> 
    show \<open>Q t\<close>
      using Q unfolding big_step_determ[OF prems(1,2)] .
  qed
qed blast+

text \<open>OHearn IMP is equivalent to incorrectness formalisation.\<close>

lemma \<open>ohearn P c Q \<longleftrightarrow> i.ohearn P c Q\<close>
  unfolding ohearn_def i.ohearn_def by auto

end
