theory Inference_Hoare
  imports "Abstract-Triples.Total_Inference" 
          "HOL-Hoare.Hoare_Logic"

begin

text \<open>Instantiate (In)correctness inferences for HOL-Hoare.\<close>

interpretation total_inference \<open>\<lambda>c s. \<exists>t. Sem c s t\<close> \<open>\<lambda>(c,s). Sem c s\<close>
  .

text \<open>Correctness\<close>

lemma \<open>Valid {a. P a} c a {a. Q a} \<longleftrightarrow> hoare P c Q\<close>
  unfolding Valid_def hoare_def by auto

text \<open>Total Correctness\<close>

lemma \<open>ValidTC {a. P a} c a {a. Q a} \<longleftrightarrow> thoare P c Q\<close>
unfolding ValidTC_def thoare_alt_def hoare_def prod.case all_simps mem_Collect_eq proof safe
  fix s t assume \<open>\<forall>s. P s \<longrightarrow> (\<exists>t. Sem c s t \<and> Q t)\<close> \<open>P s\<close> \<open>Sem c s t\<close> 
  thus \<open>Q t\<close>
  proof (elim allE[where x = s] impE exE conjE)
    fix t' assume prems: \<open>Sem c s t\<close> \<open>Sem c s t'\<close> and Q: \<open>Q t'\<close> 
    show \<open>Q t\<close>
      using Q unfolding Sem_deterministic[OF prems(1,2)] .
  qed
qed blast+

end
