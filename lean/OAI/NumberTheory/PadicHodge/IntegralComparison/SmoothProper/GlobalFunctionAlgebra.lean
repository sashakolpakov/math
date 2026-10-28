import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.GlobalFunctionsFinite
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ReducedEtale
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth

/-! # Global Function Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra

noncomputable section

/-! The actual global-function algebra of a nonempty smooth proper projective scheme over a finite field is finite étale. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))

abbrev algebra : CommAlgCat.{u} k := (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op ⊤)

theorem module_finite [IsProper X.hom] (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) : Module.Finite k (algebra k X) :=
  Projective.GlobalFunctionsFinite.finite k X hprojective

theorem finite [Finite k] [IsProper X.hom] (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) : Finite (algebra k X) := by
  let : Module.Finite k (algebra k X) := module_finite k X hprojective
  exact Module.finite_of_finite k

theorem reduced [Smooth X.hom] : _root_.IsReduced (algebra k X) := by
  let : IsReduced X.left := AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field X.hom
  exact inferInstanceAs (_root_.IsReduced Γ(X.left, ⊤))

theorem nontrivial [Nonempty X.left] : Nontrivial (algebra k X) := by
  let : Nonempty (⊤ : X.left.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  exact inferInstanceAs (Nontrivial Γ(X.left, ⊤))

variable (p : ℕ) [Fact p.Prime] [CharP k p] [Nonempty X.left]

theorem characteristic : CharP (algebra k X) p := by
  let := nontrivial k X
  exact CharP.of_ringHom_of_ne_zero (algebraMap k (algebra k X)) p (Fact.out : p.Prime).ne_zero

include p in
theorem etale [Finite k] [IsProper X.hom] [Smooth X.hom]
    (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) : Algebra.Etale k (algebra k X) := by
  let := finite k X hprojective
  let := reduced k X
  let := characteristic k X p
  exact IntegralComparison.Finite.ReducedEtale.etale p (algebra k X) k

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra
