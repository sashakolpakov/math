import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Normalized Scalar -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.NormalizedScalar.Construction.NormalizedScalarIso

noncomputable section

/-! Isomorphisms of scalar extensions characterized on the canonical generators. -/

open _root_.CategoryTheory
open scoped ChangeOfRings

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
variable {A : ModuleCat.{u} R} {B C : ModuleCat.{u} S}

abbrev Data (v : A → B) :=
  {e : (ModuleCat.extendScalars f).obj A ≅ B // ∀ s, e.hom ((1 : S) ⊗ₜ[R,f] s) = v s}

def post {v : A → B} (e : Data f v) (d : B ≅ C) : Data f (fun s => d.hom (v s)) := by
  refine ⟨e.val ≪≫ d, ?_⟩
  intro s
  exact congrArg d.hom (e.property s)

theorem isIso {v : A → B} (e : Data f v) (a : (ModuleCat.extendScalars f).obj A ⟶ B)
    (h : ∀ s, a ((1 : S) ⊗ₜ[R,f] s) = v s) : IsIso a := by
  have he : a = e.val.hom := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro s
    exact (h s).trans (e.property s).symm
  rw [he]
  infer_instance

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.NormalizedScalar.Construction.NormalizedScalarIso
