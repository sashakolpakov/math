import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationEnhancementData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.Isomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Families
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Functor

/-! # Polarization Enhancement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower

noncomputable section

/-! Polarization data compatible with a fixed power line bundle on a
full-level abelian family have a unique moduli class on Noetherian affine
bases. The representing dual is allowed to vary. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ} {F : Level.Data.AbelianSchemeWithFullLevel g N S}
variable {L : Line.Bundles.LineBundle F.abelian.scheme.left} {d : ℕ}

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable (D E : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d) (hδ : ∀ i, 0 < δ i) (hd : 0 < d)

include hδ hd

def PolarizationEnhancementData.GraphPowerPolarizationEnhancement.uniqueModuliIso : Moduli.Isomorphisms.LevelPreservingIso D.object E.object := by
  let e : D.object.abelian.scheme ≅ E.object.abelian.scheme := Iso.refl F.abelian.scheme
  letI : IsMonHom e.hom := inferInstanceAs (IsMonHom (𝟙 F.abelian.scheme))
  exact Moduli.Isomorphisms.LevelPreservingIso.ofGraphPower_noetherian_affine D.object E.object hδ e d hd
    (by
      change Line.Bundles.LineBundle.pullbackClass (𝟙 F.abelian.scheme.left)
        (Line.Bundles.LineBundle.classOf E.object.graphBundle ^ d) = Line.Bundles.LineBundle.classOf D.object.graphBundle ^ d
      rw [Line.Bundles.LineBundle.pullbackClass_id]
      have h : Line.Bundles.LineBundle.classOf (E.object.graphBundle.tensorPower d) =
          Line.Bundles.LineBundle.classOf (D.object.graphBundle.tensorPower d) :=
        Quotient.sound ⟨E.powerIso.some.symm ≪≫ D.powerIso.some⟩
      simpa only [Line.Bundles.LineBundle.classOf_tensorPower] using h)
    (fun _ _ => Category.comp_id _)

theorem PolarizationEnhancementData.GraphPowerPolarizationEnhancement.object_class_unique : D.object.classOf = E.object.classOf :=
  (D.object.classOf_eq_iff E.object).mpr ⟨D.uniqueModuliIso E hδ hd⟩

theorem PolarizationEnhancementData.GraphPowerPolarizationEnhancement.moduliClass_range_subsingleton :
    Set.Subsingleton (Set.range (fun D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d => D.object.classOf)) := by
  rintro _ ⟨D, rfl⟩ _ ⟨E, rfl⟩
  exact D.object_class_unique E hδ hd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower
