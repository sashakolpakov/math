import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleHomology

/-! # Module Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleQuasiIso

noncomputable section

/-! Actual affine principal sections preserve quasi-isomorphisms
between quasicoherent sheaf complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]

theorem preservesLeft (q : ℕ) :
    (ModuleFunctor.functor U hU).PreservesLeftHomologyOf (K.sc q) := by
  let : (K.sc q).X₁.IsQuasicoherent := inferInstanceAs (K.X ((ComplexShape.up ℕ).prev q)).IsQuasicoherent
  let : (K.sc q).X₂.IsQuasicoherent := inferInstanceAs (K.X q).IsQuasicoherent
  let : (K.sc q).X₃.IsQuasicoherent := inferInstanceAs (K.X ((ComplexShape.up ℕ).next q)).IsQuasicoherent
  exact ModuleHomology.preservesLeft U hU (K.sc q)

variable {K} {L : CochainComplex X.Modules ℕ} [∀ q, (L.X q).IsQuasicoherent]
  (a : K ⟶ L) [QuasiIso a]

theorem quasiIso : QuasiIso
    (((ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).map a) := by
  constructor
  intro q
  let := preservesLeft U hU K q
  let := preservesLeft U hU L q
  let : ShortComplex.QuasiIso ((shortComplexFunctor X.Modules (.up ℕ) q).map a) :=
    (quasiIsoAt_iff a q).mp inferInstance
  rw [quasiIsoAt_iff]
  change ShortComplex.QuasiIso ((ModuleFunctor.functor U hU).mapShortComplex.map
    ((shortComplexFunctor X.Modules (.up ℕ) q).map a))
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleQuasiIso
