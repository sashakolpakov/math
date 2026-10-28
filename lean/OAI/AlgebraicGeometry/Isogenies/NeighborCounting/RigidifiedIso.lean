import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar

/-! # Rigidified Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedIso

noncomputable section

/-! Normalize an actual line-bundle isomorphism along a section.
The correction is constructed from the induced automorphism of the
structure sheaf. No normalization equation is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar

variable {X T : Scheme.{u}} (π : X ⟶ T) (z : T ⟶ X)
variable {M N : X.Modules}

/-- The discrepancy between two chosen trivializations along the section. -/
def sectionDiscrepancy (e : M ≅ N)
    (eM : (Scheme.Modules.pullback z).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T)
    (eN : (Scheme.Modules.pullback z).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T) :
    ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T :=
  eM.symm ≪≫ (Scheme.Modules.pullback z).mapIso e ≪≫ eN

/-- Correct the discrepancy by a unit function pulled back from the base. -/
def normalizedIso (e : M ≅ N)
    (eM : (Scheme.Modules.pullback z).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T)
    (eN : (Scheme.Modules.pullback z).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T) : M ≅ N :=
  ModuleScalar.scalarIso M (Units.map π.appTop.hom
    (ModuleScalar.structureAutUnit (sectionDiscrepancy z e eM eN).symm)) ≪≫ e

theorem section_pullback_scalar (hπ : z ≫ π = 𝟙 T) (r : Γ(T, ⊤)) :
    (Scheme.Modules.pullback z).map (ModuleScalar.scalarEnd M (π.appTop r)) =
      ModuleScalar.scalarEnd ((Scheme.Modules.pullback z).obj M) r := by
  rw [ModuleScalar.scalarEnd_pullback]
  have h : z.appTop (π.appTop r) = r := by
    have he := congrArg (fun f : T ⟶ T ↦ f.appTop) hπ
    exact congrArg (fun q ↦ q r) he
  rw [h]

/-- The constructed isomorphism respects the supplied zero-section
trivializations exactly, even when the base is nonreduced. -/
theorem normalizedIso_section (hπ : z ≫ π = 𝟙 T) (e : M ≅ N)
    (eM : (Scheme.Modules.pullback z).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T)
    (eN : (Scheme.Modules.pullback z).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T) :
    (Scheme.Modules.pullback z).map (normalizedIso π z e eM eN).hom ≫ eN.hom = eM.hom := by
  let c := sectionDiscrepancy z e eM eN
  let r := ModuleScalar.structureAutUnit c.symm
  have hc : (Scheme.Modules.pullback z).map e.hom ≫ eN.hom = eM.hom ≫ c.hom := by
    dsimp [c, sectionDiscrepancy]
    simp only [Iso.hom_inv_id_assoc]
  change (Scheme.Modules.pullback z).map (ModuleScalar.scalarEnd M (π.appTop ↑r) ≫ e.hom) ≫ eN.hom = _
  rw [Functor.map_comp, section_pullback_scalar π z hπ, Category.assoc, hc,
    ← Category.assoc, ModuleScalar.scalarEnd_naturality, Category.assoc]
  have hr : ModuleScalar.scalarEnd (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T) ↑r = c.inv := ModuleScalar.scalarEnd_structureAut c.symm
  rw [hr, c.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedIso
