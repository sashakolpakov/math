import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingAction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELTransport

/-! # Marking Fiber Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Transport the actual marking-family comparison to a geometric
fiber and retain its exact abelian morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
section
variable {R : Type u} [CommRing R] {g N : ℕ} {S T : Scheme.{u}}
  {P Q : PEL.PELFamilyData R g N S} {P₀ Q₀ : PEL.PELFamilyData R g N T}
  (a : (ZMod N)ˣ) (j : PELModuli.PELFamilyIso (P.shiftMarking a) Q) (b : T ⟶ S)
  (p : PELModuli.PELFamilyIso P₀ (P.pullback b)) (r : PELModuli.PELFamilyIso Q₀ (Q.pullback b))

def PELModuli.PELFamilyIso.markingFiberTransport : PELModuli.PELFamilyIso (P₀.shiftMarking a) Q₀ :=
  (p.shiftMarking a).trans ((P.shiftMarkingPullbackIso a b).symm.trans ((j.pullback b).trans r.symm))

theorem PELModuli.PELFamilyIso.markingFiberTransport_hom :
    (PELModuli.PELFamilyIso.markingFiberTransport a j b p r).abelian.hom =
      p.abelian.hom ≫ (Over.pullback b).map j.abelian.hom ≫ r.abelian.inv := by
  change p.abelian.hom ≫ (𝟙 _ ≫ ((Over.pullback b).map j.abelian.hom ≫ r.abelian.inv)) = _
  rw [Category.id_comp]

end

variable {S : Scheme.{u}} {A B C D : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj C] [IsCommMonObj C] [GrpObj D] [IsCommMonObj D]
  (a : A ≅ B) [IsMonHom a.hom] (d : C ≅ D) (f j : B ⟶ D) (n : ℕ)

omit [IsCommMonObj A] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C] [GrpObj D] [IsCommMonObj D] in
theorem MarkingFiberTransport.multiplication_factor_of_transport
    (h : a.hom ≫ f ≫ d.inv = ((𝟙 A) ^ n) ≫ (a.hom ≫ j ≫ d.inv)) :
    f = ((𝟙 B) ^ n) ≫ j := by
  have hn : ((𝟙 A) ^ n) ≫ a.hom = a.hom ≫ ((𝟙 B) ^ n) := by
    rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  rw [← Category.assoc ((𝟙 A) ^ n) a.hom, hn] at h
  apply (cancel_epi a.hom).mp
  apply (cancel_mono d.inv).mp
  simpa only [Category.assoc] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
