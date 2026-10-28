import OAI.RepresentationTheory.Weil.AdelicSplitting.Rational

/-! # Fresnel Algebra -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelAlgebra.Construction

noncomputable section

/-! The two Fourier-quadratic words have the same symplectic matrix. -/

def unitSymmetricMatrix (k : Type) [Field k] (N : ℕ) : Local.FunctionsMetaplectic.Construction.SymmetricMatrix k N :=
  ⟨1, Matrix.isSymm_one⟩

def negativeUnitSymmetricMatrix (k : Type) [Field k] (N : ℕ) : Local.FunctionsMetaplectic.Construction.SymmetricMatrix k N :=
  ⟨-1, Matrix.isSymm_one.neg⟩

theorem fresnel_symplectic_relation (k : Type) [Field k] (N : ℕ) :
    Local.Generators.Construction.weylSymplectic k N * Local.Generators.Construction.quadraticSymplectic (unitSymmetricMatrix k N) * Local.Generators.Construction.weylSymplectic k N =
      Local.Generators.Construction.quadraticSymplectic (negativeUnitSymmetricMatrix k N) * Local.Generators.Construction.weylSymplectic k N *
        Local.Generators.Construction.quadraticSymplectic (negativeUnitSymmetricMatrix k N) := by
  apply Subtype.ext
  change (Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 1 0 1 1) * Matrix.fromBlocks 0 1 (-1) 0 =
    (Matrix.fromBlocks 1 0 (-1) 1 * Matrix.fromBlocks 0 1 (-1) 0) * Matrix.fromBlocks 1 0 (-1) 1
  simp [Matrix.fromBlocks_multiply]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelAlgebra.Construction
