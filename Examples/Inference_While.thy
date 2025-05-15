theory Inference_While
  imports "Abstract-Triples.Total_Inference" 
          "Abstract-Hoare-Logics.HoareTotal"
begin

text \<open>Instantiate total (in)correctness inferences for an abstract while language.\<close>

interpretation total_inference termi \<open>\<lambda>(c,s) t. s -c\<rightarrow> t\<close>
  .

text \<open>Hoare IMP is equivalent to correctness formalisation.\<close>

lemma hoare_equiv: \<open>hoare_valid P c Q \<longleftrightarrow> hoare P c Q\<close>
  unfolding hoare_valid_def hoare_def by auto

lemma \<open>hoare_tvalid P c Q \<longleftrightarrow> thoare P c Q\<close>
  unfolding hoare_tvalid_def thoare_def hoare_equiv ..

end
