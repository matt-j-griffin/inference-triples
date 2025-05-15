chapter AFP

session "Abstract-Triples" = HOL +
  description "
    Abstract Hoare/O'Hearn triples for (in)correctness.
  "
  options [timeout = 600]
  theories
    Total_Inference
  document_files
    "root.bib"
    "root.tex"


session "Abstract-Triples-Examples" in Examples = "Abstract-Triples" +
  options [timeout = 600]
  sessions
    HoareForDivergence
    "HOL-Hoare"
    "HOL-IMP"
    "HOL-IMPP"
    "HOL-Hoare_Parallel"
    "HOL-Hoare_Parallel"
    "Relational-Incorrectness-Logic"
    "Abstract-Hoare-Logics"
  theories [document = false]
    "Inference_For_Divergence"
    "Inference_Hoare"
    "Inference_IMP"
    "Inference_IMPP"
    "Inference_OG"
    "Inference_PsWhile"
    "Inference_PWhile"
    "Inference_RG"
    "Inference_While"
