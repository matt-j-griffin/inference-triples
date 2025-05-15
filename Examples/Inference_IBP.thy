theory Inference_IBP
  imports "../Inference" 
          "DataRefinementIBP.Hoare"
begin

text \<open>Instantiate (In)correctness inferences for IBP.\<close>

interpretation inference \<open>\<lambda>(c,s) t. t = c s\<close>
  .

text \<open>Refinement IBP is equivalent to correctness formalisation.\<close>

lemma \<open>hoare (\<lambda>_. True) c (\<lambda>_. P \<sqsubseteq> c Q) \<longleftrightarrow> \<Turnstile> (P){| c |}(Q)\<close>
  unfolding hoare_def case_prod_beta fst_conv snd_conv Hoare_def
  by auto


interpretation inference \<open>\<lambda>(c,s) t. True\<close>
  .

text \<open>Refinement IBP is equivalent to correctness formalisation.\<close>

lemma \<open>hoare (\<lambda>_. True) c (\<lambda>_. P \<sqsubseteq> c Q) \<longleftrightarrow> \<Turnstile> (P){| c |}(Q)\<close>
  unfolding hoare_def case_prod_beta fst_conv snd_conv Hoare_def
  by auto

end