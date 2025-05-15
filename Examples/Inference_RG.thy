theory Inference_RG
  imports "Abstract-Triples.Inference" 
          "HOL-Hoare_Parallel.RG_Hoare"
begin

text \<open>Instantiate (In)correctness inferences for HOL-IMP.\<close>

interpretation inference \<open>\<lambda>(c,x) t. (\<exists>s. x \<in> cp (Some c) s) \<and> x = t\<close>
  .

text \<open>Rely Guarantee Hoare is equivalent to correctness formalisation.\<close>

lemma \<open>hoare (\<lambda>s. s \<in> assum (P, rely)) c (\<lambda>t. t \<in> comm (guar, Q)) \<longleftrightarrow> \<Turnstile> c sat [P, rely, guar, Q]\<close>
  unfolding hoare_def case_prod_beta fst_conv snd_conv com_validity_def by auto

end
