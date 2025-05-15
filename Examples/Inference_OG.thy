theory Inference_OG
  imports "Abstract-Triples.Inference" 
          "HOL-Hoare_Parallel.OG_Tran"
begin

text \<open>Instantiate (In)correctness inferences for HOL-IMP.\<close>

interpretation inference \<open>\<lambda>(c,s) t. \<exists>Ts. (c, s) -P*\<rightarrow> (Parallel Ts, t) \<and> All_None Ts\<close>
  .

text \<open>Owicki Greis Hoare Logic is equivalent to correctness formalisation.\<close>

lemma \<open>hoare (\<lambda>s. s \<in> P) c (\<lambda>t. t \<in> Q) \<longleftrightarrow> \<parallel>= P c Q\<close>
  unfolding hoare_def case_prod_beta fst_conv snd_conv com_validity_def
  unfolding SEM_def sem_def by auto

end
