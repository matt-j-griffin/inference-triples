theory Total_Inference
  imports Inference Total_Correctness
begin

locale total_inference = inference big_step + total_correctness big_step
  for big_step :: \<open>('prog \<times> 'state) \<Rightarrow> 'state \<Rightarrow> bool\<close> (infix \<open>\<Rightarrow>\<close> 55)

end
