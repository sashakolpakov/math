import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulHomotopy

/-! # Koszul Cone -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulCone

noncomputable section

/-! The exterior Koszul complex is the genuine scalar homotopy cofiber after
splitting off one coordinate. The comparison retains its wedge orientation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulComplex
  KoszulHomotopy

universe u

@[reassoc]
private theorem inl_biprodIsoProd (R : Type u) [CommRing R]
    (M N : ModuleCat.{u} R) : biprod.inl ≫ (ModuleCat.biprodIsoProd M N).hom =
      ModuleCat.ofHom (LinearMap.inl R M N) := by
  rw [← cancel_mono (ModuleCat.biprodIsoProd M N).inv, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext <;> simp <;> rfl

@[reassoc]
private theorem inr_biprodIsoProd (R : Type u) [CommRing R]
    (M N : ModuleCat.{u} R) : biprod.inr ≫ (ModuleCat.biprodIsoProd M N).hom =
      ModuleCat.ofHom (LinearMap.inr R M N) := by
  rw [← cancel_mono (ModuleCat.biprodIsoProd M N).inv, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext <;> simp <;> rfl

variable (R V : Type u) [CommRing R] [AddCommGroup V] [Module R V]
  (s l : Module.Dual R V) (e : V)
  (W : Type u) [AddCommGroup W] [Module R W] (t : Module.Dual R W)
  (f : W →ₗ[R] V) (g : V →ₗ[R] W)
  (hf : s.comp f = t)
  (hgf : g.comp f = LinearMap.id)
  (hfg : f.comp g = CoordinateSplit.projection R V l e)
  (hle : l e = 1) (hlf : l.comp f = 0) (hge : g e = 0)

def successorIso (n : ℕ) :
    (homotopyCofiber (s e • 𝟙 (KoszulComplex.complex R W t))).X (n + 1) ≅
      (KoszulComplex.complex R V s).X (n + 1) :=
  homotopyCofiber.XIsoBiprod (s e • 𝟙 (KoszulComplex.complex R W t)) (n + 1) n rfl ≪≫
    ModuleCat.biprodIsoProd (ModuleCat.of R (⋀[R]^n W))
      (ModuleCat.of R (⋀[R]^(n + 1) W)) ≪≫
      (CoordinateSplit.equiv R V l e W f g hgf hfg hle hlf hge n).toModuleIso

theorem coneMap_succ (n : ℕ) :
    (KoszulHomotopy.coneMap R V s e W t f hf).f (n + 1) =
      (successorIso R V s l e W t f g hgf hfg hle hlf hge n).hom := by
  apply homotopyCofiber.ext_from_X (s e • 𝟙 (KoszulComplex.complex R W t)) n (n + 1) rfl
  · rw [KoszulHomotopy.inl_coneMap]
    dsimp only [successorIso, Iso.trans_hom]
    erw [homotopyCofiber.inlX_XIsoBiprod_hom_assoc, inl_biprodIsoProd_assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n (exteriorPower.map n f x) =
      AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n (exteriorPower.map n f x) + exteriorPower.map (n + 1) f 0
    simp
  · rw [KoszulHomotopy.inr_coneMap]
    dsimp only [successorIso, Iso.trans_hom]
    erw [homotopyCofiber.inrX_XIsoBiprod_hom_assoc, inr_biprodIsoProd_assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change exteriorPower.map (n + 1) f x =
      AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n (exteriorPower.map n f 0) + exteriorPower.map (n + 1) f x
    simp

def zeroIso : (homotopyCofiber (s e • 𝟙 (KoszulComplex.complex R W t))).X 0 ≅
    (KoszulComplex.complex R V s).X 0 :=
  homotopyCofiber.XIso (s e • 𝟙 (KoszulComplex.complex R W t)) 0 (by intro h; change _ + 1 = 0 at h; omega) ≪≫
    ((exteriorPower.zeroEquiv R W).trans (exteriorPower.zeroEquiv R V).symm).toModuleIso

theorem coneMap_zero : (KoszulHomotopy.coneMap R V s e W t f hf).f 0 =
    (zeroIso R V s e W t).hom := by
  apply homotopyCofiber.ext_from_X' (s e • 𝟙 (KoszulComplex.complex R W t)) 0
    (by intro h; change _ + 1 = 0 at h; omega)
  rw [KoszulHomotopy.inr_coneMap]
  dsimp only [zeroIso, Iso.trans_hom]
  have hno : ¬ (ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := by
    intro h; change _ + 1 = 0 at h; omega
  simp only [homotopyCofiber.inrX, dite_eq_right hno, Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (exteriorPower.zeroEquiv R V).injective
  exact (LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality f) x).trans
    (by simp)

include hgf hfg hle hlf hge in
theorem coneMap_isIso : IsIso (KoszulHomotopy.coneMap R V s e W t f hf) := by
  have : ∀ n, IsIso ((KoszulHomotopy.coneMap R V s e W t f hf).f n) := fun n => by
    cases n with
    | zero => rw [coneMap_zero]; infer_instance
    | succ n => rw [coneMap_succ R V s l e W t f g hf hgf hfg hle hlf hge]; infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

def iso : homotopyCofiber (s e • 𝟙 (KoszulComplex.complex R W t)) ≅ KoszulComplex.complex R V s := by
  letI := coneMap_isIso R V s l e W t f g hf hgf hfg hle hlf hge
  exact asIso (KoszulHomotopy.coneMap R V s e W t f hf)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulCone
