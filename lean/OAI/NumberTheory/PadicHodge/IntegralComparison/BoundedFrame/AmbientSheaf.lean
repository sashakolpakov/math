import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureDescent
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FreePresheafBiproduct

/-! # Ambient Sheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.AmbientSheaf

noncomputable section

/-!
# IntegralComparison: the native product ambient-ring sheaf is the frame slice direct image
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FreePresheafBiproduct.ambientPresheaf H
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.coefficientPresheaves (p := p) (J := J) (δ := δ) f n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n

abbrev ambientSheaf : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n :=
  (Bounded.SliceImage.directImage f n F).obj (BoundedCrystalline.SliceSheaves.structureSheaf f n F)

def presheafIso : (L).obj A ≅ (ambientSheaf f n F).obj :=
  Functor.isoWhiskerLeft (H).op (Crystalline.StructureDescent.structurePresheafIso f)

def sheafIso : (S).obj A ≅ ambientSheaf f n F :=
  (presheafToSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapIso (presheafIso f n F) ≪≫
    (CategoryTheory.sheafificationIso (ambientSheaf f n F)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.AmbientSheaf
