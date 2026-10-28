import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.AffineNilLift

/-! # Affine Scheme Nil Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.AffineSchemeNilLift

noncomputable section

/-! An actual etale morphism between affine schemes has the unique
lifting property against affine nilpotent closed thickenings. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y T T₀ : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine T] [IsAffine T₀]
  (f : Y ⟶ X) [Etale f] (i : T₀ ⟶ T) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker) (a : T₀ ⟶ Y) (b : T ⟶ X) (hab : a ≫ f = i ≫ b)

include hi hab in
theorem existsUnique_lift : ∃! l : T ⟶ Y, i ≫ l = a ∧ l ≫ f = b := by
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra.Etale Γ(X, ⊤) Γ(Y, ⊤) := by
    change f.appTop.hom.Etale
    simpa [Scheme.Hom.appTop, Scheme.Hom.appLE] using
      f.etale_appLE (isAffineOpen_top X) (isAffineOpen_top Y) (by simp)
  have hs : Function.Surjective i.appTop.hom := by
    change Function.Surjective i.appTop
    simpa [Scheme.Hom.appTop] using i.app_surjective ⊤ (isAffineOpen_top T)
  have hn : ∀ x ∈ RingHom.ker i.appTop.hom, IsNilpotent x := by
    obtain ⟨N, hN⟩ := hi
    have hpow : RingHom.ker i.appTop.hom ^ N = 0 := by
      simpa [Scheme.Hom.appTop] using congrArg
        (fun I : T.IdealSheafData => I.ideal ⟨⊤, isAffineOpen_top T⟩) hN
    intro x hx
    refine ⟨N, ?_⟩
    have hm := Ideal.pow_mem_pow hx N
    rw [hpow] at hm
    exact hm
  have hh : Spec.map a.appTop ≫ Spec.map f.appTop = Spec.map i.appTop ≫ Spec.map b.appTop := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hab]
  obtain ⟨l, hl, _⟩ := AffineNilLift.existsUnique_lift
    Γ(X, ⊤) Γ(Y, ⊤) Γ(T, ⊤) Γ(T₀, ⊤) i.appTop.hom hs hn
    (Spec.map b.appTop) (Spec.map a.appTop) hh
  change Spec.map i.appTop ≫ l = Spec.map a.appTop ∧
    l ≫ Spec.map f.appTop = Spec.map b.appTop at hl
  have hred : i ≫ (T.isoSpec.hom ≫ l ≫ Y.isoSpec.inv) = a := by
    rw [← Scheme.isoSpec_hom_naturality_assoc,
      ← Category.assoc (Spec.map i.appTop) l, hl.1,
      Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  have hbase : (T.isoSpec.hom ≫ l ≫ Y.isoSpec.inv) ≫ f = b := by
    rw [Category.assoc, Category.assoc, ← Scheme.isoSpec_inv_naturality,
      ← Category.assoc l, hl.2, Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  refine ⟨T.isoSpec.hom ≫ l ≫ Y.isoSpec.inv, ⟨hred, hbase⟩, ?_⟩
  intro l' hl'
  exact FormallyUnramified.hom_ext i hi f (hl'.1.trans hred.symm) (hl'.2.trans hbase.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.AffineSchemeNilLift
