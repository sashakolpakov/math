import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberScalar
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PureTensor

/-! # Fiber Tensor -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberTensor

noncomputable section

/-! A model cycle surviving in the local residue tensor survives in the
canonical scalar extension along the actual geometric fiber. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

namespace Construction.FiberTensorSurvival

variable (S : Scheme.{u}) (x : S) (M : ModuleCat.{u} Γ(S, ⊤)) (m : M)

theorem nonzero (h : letI : Algebra Γ(S, ⊤) (S.presheaf.stalk x) :=
      (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
    (1 : IsLocalRing.ResidueField (S.presheaf.stalk x)) ⊗ₜ[S.presheaf.stalk x]
      ((1 : S.presheaf.stalk x) ⊗ₜ[Γ(S, ⊤)] m) ≠ 0) :
    ((1 : Γ(Spec (S.residueField x), ⊤)) ⊗ₜ[Γ(S, ⊤),(S.fromSpecResidueField x).appTop.hom] m :
      (ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).obj M) ≠ 0 := by
  let R := Γ(S, ⊤)
  let A := S.presheaf.stalk x
  let K := IsLocalRing.ResidueField A
  let f : R →+* A := (S.presheaf.germ ⊤ x trivial).hom
  let g : A →+* K := (S.residue x).hom
  let : Algebra R A := f.toAlgebra
  let : Algebra R K := (g.comp f).toAlgebra
  have : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have hn : ((1 : K) ⊗ₜ[R,g.comp f] m : (ModuleCat.extendScalars (g.comp f)).obj M) ≠ 0 :=
    PureTensor.Construction.PureTensorSurvival.nested_ne_zero (R := R) (S := A) (A := K) M m h
  have he : (Scheme.ΓSpecIso (.of K)).hom.hom.comp (S.fromSpecResidueField x).appTop.hom = g.comp f :=
    congrArg (fun a : Γ(S, ⊤) ⟶ S.residueField x => a.hom)
      (FiberScalar.Construction.FiberScalarMaps.fromResidue_appTop S x)
  intro hz
  have hzero := PureTensor.Construction.PureTensorSurvival.zero_comp (S.fromSpecResidueField x).appTop.hom
    (Scheme.ΓSpecIso (.of K)).hom.hom M m hz
  rw [he] at hzero
  exact hn hzero

end Construction.FiberTensorSurvival

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberTensor
