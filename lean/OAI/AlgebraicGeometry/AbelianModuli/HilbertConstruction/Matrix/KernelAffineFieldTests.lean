import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.MatrixRankScalarExtension

/-! # Kernel Affine Field Tests -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.KernelAffineFieldTests

noncomputable section

/-! Matrix kernel-dimension opens have their expected criterion in the coefficient field of an affine test point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {μ ν : Type u} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]

theorem matrixKernelDimensionOpen_field_coefficients {X : Scheme.{u}} {K : Type u} [Field K]
    (c : Spec (.of K) ⟶ X) (B : Matrix ν μ Γ(X, ⊤)) (d : ℕ) :
    Set.range c ⊆ (KernelDimensionOpen.matrixKernelDimensionOpen B d : Set X) ↔
      Module.finrank K (Matrix.toLin'
        (B.map ((Scheme.ΓSpecIso (.of K)).hom.hom.comp c.appTop.hom))).ker ≤ d := by
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)).toField
  have he := HilbertConstruction.Field.MatrixRankScalarExtension.fieldMatrix_kernel_finrank_map (Scheme.ΓSpecIso (.of K)).hom.hom (B.map c.appTop.hom)
  exact (KernelDimensionOpen.matrixKernelDimensionOpen_field_point c B d).trans
    (congrArg (fun q : ℕ => q ≤ d) he.symm).to_iff

theorem matrixKernelDimensionOpen_specMap {R K : Type u} [CommRing R] [Field K]
    (φ : R →+* K) (B : Matrix ν μ R) (d : ℕ) :
    Set.range (Spec.map (CommRingCat.ofHom φ)) ⊆
      (KernelDimensionOpen.matrixKernelDimensionOpen (B.map (Scheme.ΓSpecIso (.of R)).inv.hom) d : Set (Spec (.of R))) ↔
        Module.finrank K (Matrix.toLin' (B.map φ)).ker ≤ d := by
  have he : (B.map (Scheme.ΓSpecIso (.of R)).inv.hom).map
      ((Scheme.ΓSpecIso (.of K)).hom.hom.comp (Spec.map (CommRingCat.ofHom φ)).appTop.hom) = B.map φ := by
    ext i j
    have hc := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)) (B i j)
    exact (congrArg (fun z => (Scheme.ΓSpecIso (.of K)).hom z) hc).symm.trans
      ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.apply_symm_apply (φ (B i j)))
  exact (matrixKernelDimensionOpen_field_coefficients (Spec.map (CommRingCat.ofHom φ))
    (B.map (Scheme.ΓSpecIso (.of R)).inv.hom) d).trans
    (congrArg (fun A : Matrix ν μ K => Module.finrank K (Matrix.toLin' A).ker ≤ d) he).to_iff

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.KernelAffineFieldTests
