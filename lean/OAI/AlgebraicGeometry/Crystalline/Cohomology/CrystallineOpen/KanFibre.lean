import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Topology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ResidualCover
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-! # Kan Fibre -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.KanFibre.CrystallineOpenKanFibre

noncomputable section

/-!
# The Zariski direct-image fibre is the actual open crystalline site

The comma category defining right Kan extension at the image of an open
immersion is equivalent to the opposite crystalline site of that open.
The comparison uses the previously constructed native lifts and preserves
the actual ambient coefficient diagram.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X Y : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]

local notation "Inclusion" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Embedding.CrystallineOpenEmbedding.functor p k j
local notation "Residual" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ResidualCover.CrystallineResidualCover.functor p k Y
local notation "Comma" => StructuredArrow (op (Scheme.Hom.opensRange (Over.Hom.left j))) (Functor.op Residual)

def object (Q : (Site.Object p k X)ᵒᵖ) : Comma :=
  StructuredArrow.mk (Y := (Inclusion).op.obj Q) (homOfLE (by
    rintro y ⟨z, rfl⟩
    exact ⟨Q.unop.immersion z, rfl⟩)).op

def functor : (Site.Object p k X)ᵒᵖ ⥤ Comma where
  obj := object p k j
  map f := StructuredArrow.homMk ((Inclusion).op.map f) (Subsingleton.elim _ _)
  map_id _ := StructuredArrow.hom_ext _ _ ((Inclusion).op.map_id _)
  map_comp _ _ := StructuredArrow.hom_ext _ _ ((Inclusion).op.map_comp _ _)

def fullyFaithful : (functor p k j).FullyFaithful where
  preimage f := (Inclusion).op.preimage f.right
  map_preimage f := by
    apply StructuredArrow.hom_ext
    exact (Inclusion).op.map_preimage f.right
  preimage_map f := Functor.preimage_map (F := (Inclusion).op) f

instance full : (functor p k j).Full := (fullyFaithful p k j).full

instance faithful : (functor p k j).Faithful := (fullyFaithful p k j).faithful

def lift (T : Comma) : Site.Object p k X :=
  OpenLift.CrystallineOpenLift.object p k j T.right.unop (leOfHom T.hom.unop)

def imageIso (T : Comma) : (functor p k j).obj (op (lift p k j T)) ≅ T :=
  StructuredArrow.isoMk
    (OpenLift.CrystallineOpenLift.iso p k j T.right.unop (leOfHom T.hom.unop)).op.symm
    (Subsingleton.elim _ _)

instance essSurj : (functor p k j).EssSurj where
  mem_essImage T := ⟨op (lift p k j T), ⟨imageIso p k j T⟩⟩

instance isEquivalence : (functor p k j).IsEquivalence where

def equivalence : (Site.Object p k X)ᵒᵖ ≌ Comma :=
  (functor p k j).asEquivalence

def projectionIso : functor p k j ⋙ StructuredArrow.proj (op j.left.opensRange) (Residual).op ≅
    (Inclusion).op :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.KanFibre.CrystallineOpenKanFibre
