theory Inference_PsWhile
  imports "Abstract-Triples.Total_Inference" 
          "Abstract-Hoare-Logics.PsHoareTotal"
begin

text \<open>Instantiate total (in)correctness inferences for an abstract 1 procedure language.\<close>

interpretation i: total_inference \<open>\<lambda>c (_,s). termi c s\<close> \<open>\<lambda>(c,(z1,s)) (z2,t). z1 = z2 \<and> exec s c t\<close>
  .

text \<open>Hoare IMP is equivalent to correctness formalisation.\<close>

lemma hoare_equiv: \<open>valid P c Q \<longleftrightarrow> i.hoare (\<lambda>(z,s). P z s) c (\<lambda>(z,t). Q z t)\<close>
  unfolding valid_def i.hoare_def prod.case case_prod_beta prod.sel by auto
   
lemma \<open>tvalid P c Q \<longleftrightarrow> i.thoare (\<lambda>(z,s). P z s) c (\<lambda>(z,t). Q z t)\<close>
  unfolding tvalid_def i.thoare_def hoare_equiv by simp

end
