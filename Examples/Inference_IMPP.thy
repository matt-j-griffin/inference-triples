theory Inference_IMPP
  imports "Abstract-Triples.Inference" 
          "HOL-IMPP.Hoare"
begin

text \<open>Instantiate (In)correctness inferences for HOL-IMP.\<close>

interpretation inference \<open>\<lambda>((c,n),s) t. <c,s> -n-> t\<close>
  .

text \<open>Hoare IMPP is equivalent to correctness formalisation.\<close>

lemma \<open>(\<forall>Z. hoare (P Z) (c,n) (Q Z)) \<longleftrightarrow> |=n:{P}.c.{Q}\<close>
  unfolding triple_valid_def2 hoare_def case_prod_beta fst_conv snd_conv by auto

end
