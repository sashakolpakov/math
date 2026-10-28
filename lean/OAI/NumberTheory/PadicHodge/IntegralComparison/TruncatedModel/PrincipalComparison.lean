import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIncomingMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalPrincipal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingSectionHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Composition

/-! # Principal Comparison -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.Coordinates

/-! The original global principal comparison is the local PD map
followed by the actual incoming-frame comparison on sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.localSections p k n X Y f U
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.iso p k n X Y f U

omit [IsProper X.hom] in
theorem local_map : PrincipalIncomingBase.Map.localSource p k n X Y f hp U =
    LocalPrincipal.PDNaturality.map p k n X Y f hp U := rfl

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev comparison := Incoming.Composition.Comparison.factorization
  ((NatIso.mapHomologicalComplex e (.up ℕ)).app ((P).obj (op U)))
  ((NatIso.mapHomologicalComplex e (.up ℕ)).app I.cocomplex)
  _ _ _
  (PrincipalIncomingMap.factorization p k n X Y f hp U I)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.Coordinates

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.TypedMaps

/-! The original principal comparison arrows with one shared, explicit
type for the section complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.opens p k n X Y f U
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.globalSections (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n O
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.source p k n X Y f hp U

def localMap : L ⟶ ((S).mapHomologicalComplex (.up ℕ)).obj ((P).obj (op U)) :=
  LocalPrincipal.PDNaturality.map p k n X Y f hp U

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def incomingMap : ((S).mapHomologicalComplex (.up ℕ)).obj ((P).obj (op U)) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  IncomingSectionHomotopy.source p k n X Y f hp U I

def comparisonMap : L ⟶ ((S).mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  Principal.Comparison.map p k n X Y f hp U I

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.TypedMaps

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.IncomingCoordinates

/-! The typed incoming arrow in the original principal section coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.opens p k n X Y f U
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.globalSections (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n O
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.iso p k n X Y f U
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.localSections p k n X Y f U

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def raw : ((S).mapHomologicalComplex (.up ℕ)).obj ((P).obj (op U)) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  ((NatIso.mapHomologicalComplex e (.up ℕ)).app ((P).obj (op U))).hom ≫
    ((T).mapHomologicalComplex (.up ℕ)).map
      (Incoming.Comparison.map p k n X Y f hp U I) ≫
        ((NatIso.mapHomologicalComplex e (.up ℕ)).app I.cocomplex).inv

theorem incoming :
    TypedMaps.incomingMap p k n X Y f hp U I =
      raw p k n X Y f hp U I := rfl

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.IncomingCoordinates

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.MapCoordinates

/-! Separate coordinate identities for the original arrows in the
principal comparison factorization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

theorem comparison :
    TypedMaps.comparisonMap p k n X Y f hp U I =
      Principal.Comparison.map p k n X Y f hp U I := rfl

omit [IsProper X.hom] in
theorem local_map :
    TypedMaps.localMap p k n X Y f hp U =
      PrincipalIncomingBase.Map.localSource p k n X Y f hp U :=
  (Coordinates.local_map p k n X Y f hp U).symm

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.MapCoordinates

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.ReferenceIncoming

/-! The incoming conjugate in its original inferred native types. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.iso p k n X Y f U
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.localSections p k n X Y f U
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.opens p k n X Y f U
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.globalSections (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n O

def map : ((S).mapHomologicalComplex (.up ℕ)).obj ((P).obj (op U)) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  ((NatIso.mapHomologicalComplex e (.up ℕ)).app ((P).obj (op U))).hom ≫
    ((T).mapHomologicalComplex (.up ℕ)).map
      (Incoming.Comparison.map p k n X Y f hp U I) ≫
        ((NatIso.mapHomologicalComplex e (.up ℕ)).app I.cocomplex).inv

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.ReferenceIncoming

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.MapCoordinates

/-! The two cached incoming arrows are the same original conjugate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

theorem incoming :
    IncomingCoordinates.raw p k n X Y f hp U I =
      ReferenceIncoming.map p k n X Y f hp U I := rfl

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.MapCoordinates

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.ComponentFactorization

/-! Cancel the original incoming-section coordinate isomorphism
at each actual degree and principal open before assembling the complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (q : ℕ) (r : (PrincipalFrame.Index X.left U)ᵒᵖ)

local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.iso p k n X Y f U
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.localSections p k n X Y f U

abbrev component := Incoming.Composition.Comparison.factorization
  (((HomologicalComplex.eval _ (.up ℕ) q).mapIso
    ((NatIso.mapHomologicalComplex e (.up ℕ)).app ((P).obj (op U)))).app r)
  (((HomologicalComplex.eval _ (.up ℕ) q).mapIso
    ((NatIso.mapHomologicalComplex e (.up ℕ)).app I.cocomplex)).app r)
  (((((T).mapHomologicalComplex (.up ℕ)).map
    (Incoming.Comparison.map p k n X Y f hp U I)).f q).app r)
  (((PrincipalIncomingBase.Map.localSource p k n X Y f hp U).f q).app r)
  (((Principal.Comparison.map p k n X Y f hp U I).f q).app r)
  (PrincipalIncomingComponents.Map.factorization_component p k n X Y f hp U I q r)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.ComponentFactorization

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.RawFactorization

/-! The checked original factorization with explicitly typed arrows,
before replacing the incoming comparison by its equivalent notation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

theorem component (q : ℕ) (r : (PrincipalFrame.Index X.left U)ᵒᵖ) :
    ((TypedMaps.comparisonMap p k n X Y f hp U I).f q).app r =
      (((TypedMaps.localMap p k n X Y f hp U ≫
        IncomingCoordinates.raw p k n X Y f hp U I).f q).app r) :=
  ComponentFactorization.component p k n X Y f hp U I q r

abbrev comparison := HomologicalComplex.hom_ext
  (TypedMaps.comparisonMap p k n X Y f hp U I)
  (TypedMaps.localMap p k n X Y f hp U ≫
    IncomingCoordinates.raw p k n X Y f hp U I)
  (fun q => NatTrans.ext (funext (fun r => component p k n X Y f hp U I q r)))

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.RawFactorization

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.Identity

/-! Typed native endpoints for the original principal comparison
factorization, retaining the actual PD and incoming-section maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

theorem comparison :
    TypedMaps.comparisonMap p k n X Y f hp U I =
      TypedMaps.localMap p k n X Y f hp U ≫
        TypedMaps.incomingMap p k n X Y f hp U I :=
  (RawFactorization.comparison p k n X Y f hp U I).trans
    (congrArg (fun a => TypedMaps.localMap p k n X Y f hp U ≫ a)
      (IncomingCoordinates.incoming p k n X Y f hp U I).symm)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison.Identity

end

end OAI
