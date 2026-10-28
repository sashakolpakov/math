import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexNaturality

/-! # Complex Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexQuasiIso

noncomputable section

/-! Quasi-isomorphism transport through the canonical section map is proved
before specializing either coefficient complex. -/

open _root_.CategoryTheory

private theorem source_iso {A : Type*} [Category A] [Abelian A]
    {K L T : CochainComplex A ℕ} (u : K ⟶ L) (f : K ⟶ T) (g : L ⟶ T)
    (h : f = u ≫ g) (hu : IsIso u) : QuasiIso f ↔ QuasiIso g := by
  let := hu
  rw [h]
  exact quasiIso_iff_comp_left _ _

private theorem transported_square {C : Type*} [Category C] {A A' K L I : C}
    (u : A ⟶ A') (a : A ⟶ K) (b : A' ⟶ L) (t : K ≅ L) (g : K ⟶ I)
    (h : a ≫ t.hom = u ≫ b) : u ≫ (b ≫ t.inv ≫ g) = a ≫ g := by
  calc
    _ = (u ≫ b) ≫ t.inv ≫ g := by simp only [Category.assoc]
    _ = (a ≫ t.hom) ≫ t.inv ≫ g := by rw [h]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id_assoc]

universe u v w z
variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  {D D' : CochainComplex (ModuleCat.{w} R) ℕ}
  {K K' : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ}
  (e : D ≅ D') (g : K ⟶ K')
  (a : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ)).obj D ⟶ K)
  (a' : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ)).obj D' ⟶ K')
  (hc : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ)).map e.hom ≫ a' = a ≫ g)

abbrev naturality := source_iso _ _ _
  (ComplexNaturality.naturality.{u,v,w,z} R J e.hom g a a' hc)
  ((((ModuleCat.uliftFunctor.{z,w} R).mapHomologicalComplex (.up ℕ)).mapIso e).isIso_hom)

variable {L : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ}
  (t : K ≅ L)
  (b : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ)).obj D' ⟶ L)
  (h : a ≫ t.hom =
    ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ)).map e.hom ≫ b)

abbrev transported := naturality R J e g a (b ≫ t.inv ≫ g)
  (transported_square _ a b t g h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexQuasiIso
