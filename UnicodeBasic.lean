/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types
public import UnicodeBasic.TableLookup

/-!
  # General API #

  As a general rule, for a given a Unicode property called `Unicode_Property`,
  for example:

  - If the property is boolean valued then the implementation is called
    `Unicode.isUnicodeProperty`.

  - Otherwise, the implementation is called `Unicode.getUnicodeProperty`.

  - If the value is not of standard type (`Bool`, `Char`, `Nat`, `Int`, etc.)
    or a combination thereof (e.g. `Bool × Option Nat`) then the value type is
    defined in `UnicodeBasic.Types`.

  - If the input type needs disambiguation (e.g. `Char` vs `String`) the type
    name may be appended to the name as in `Unicode.isUnicodePropertyChar` or
    in `Unicode.getUnicodePropertyString`.

  - If the output type is `Option _` then the suffix `?` may be appended to
    indicate that this is a partial function. In this case, a companion
    function with the suffix `!` may be implemented. This function will
    perform the same calculation as the original but it assumes the user has
    checked that the input is in the domain, the function may panic if this
    is not the case.

  Unicode general categories are encoded using the type `GC`. This type has
  a boolean algebra structure with inclusion `⊆`, meet/intersection `&&&`,
  join/union `|||` and complement `~~~`. The relation `∈` is provided to
  check whether a character belongs to a given category. For example,
  `c ∈ (GC.L &&& ~~~GC.Lt) ||| GC.Z` checks whether `c` is a either a
  non-titlecase letter or a separator.
-/

namespace Unicode

/-!
  ## Name ##
-/

/-- Get character name

  When the Unicode property `Name` is empty, a unique code label is returned
  as recommended in Unicode Standard, section 4.8. These labels start with
  `'<'` (U+003C) and end with `'>'` (U+003E) so they are distinguishable from
  actual name values.

  Unicode property: `Name`
-/
@[inline]
public def getName (char : Char) : String := lookupName char.val

/-!
  ## Script ##
-/

/-- Get character script

  Unicode property: `Script`
-/
@[inline]
public def getScript (char : Char) : Script := lookupScript char.val

/-- Get script name

  Returns `none` if the script code is unassigned.

  Unicode property: `Script`
-/
@[inline]
public def getScriptName? (s : Script) : Option String :=
  lookupScriptName s |>.map toString

/-- Get character script extensions

  Unicode property: `Script_Extensions`
-/
@[inline]
public def getScriptExtensions (char : Char) : Array Script :=
  let scs := lookupScriptExtensions char.val
  if scs.isEmpty then #[lookupScript char.val] else scs

/-- Check if character is part of a script

  This function checks the `Script` property of the character.
-/
@[inline]
public def isScript (sc : Script) (char : Char) : Bool :=
  lookupScript char.val == sc

/-- Check if character has a script extension

  This function checks the `Script_Extensions` property of the character.
  The `Script_Extensions` property includes the `Script` property.
-/
@[inline]
public def hasScript (sc : Script) (char : Char) : Bool :=
  getScriptExtensions char |>.contains sc

/-- Check if character is Adlam -/
public def isAdlam (char : Char) : Bool := isScript (Script.ofAbbrev! "Adlm") char
/-- Check if character is Ahom -/
public def isAhom (char : Char) : Bool := isScript (Script.ofAbbrev! "Ahom") char
/-- Check if character is Anatolian_Hieroglyphs -/
public def isAnatolianHieroglyphs (char : Char) : Bool := isScript (Script.ofAbbrev! "Hluw") char
/-- Check if character is Arabic -/
public def isArabic (char : Char) : Bool := isScript (Script.ofAbbrev! "Arab") char
/-- Check if character is Armenian -/
public def isArmenian (char : Char) : Bool := isScript (Script.ofAbbrev! "Armn") char
/-- Check if character is Avestan -/
public def isAvestan (char : Char) : Bool := isScript (Script.ofAbbrev! "Avst") char
/-- Check if character is Balinese -/
public def isBalinese (char : Char) : Bool := isScript (Script.ofAbbrev! "Bali") char
/-- Check if character is Bamum -/
public def isBamum (char : Char) : Bool := isScript (Script.ofAbbrev! "Bamu") char
/-- Check if character is Bassa_Vah -/
public def isBassaVah (char : Char) : Bool := isScript (Script.ofAbbrev! "Bass") char
/-- Check if character is Batak -/
public def isBatak (char : Char) : Bool := isScript (Script.ofAbbrev! "Batk") char
/-- Check if character is Bengali -/
public def isBengali (char : Char) : Bool := isScript (Script.ofAbbrev! "Beng") char
/-- Check if character is Beria_Erfe -/
public def isBeriaErfe (char : Char) : Bool := isScript (Script.ofAbbrev! "Berf") char
/-- Check if character is Bhaiksuki -/
public def isBhaiksuki (char : Char) : Bool := isScript (Script.ofAbbrev! "Bhks") char
/-- Check if character is Bopomofo -/
public def isBopomofo (char : Char) : Bool := isScript (Script.ofAbbrev! "Bopo") char
/-- Check if character is Brahmi -/
public def isBrahmi (char : Char) : Bool := isScript (Script.ofAbbrev! "Brah") char
/-- Check if character is Braille -/
public def isBraille (char : Char) : Bool := isScript (Script.ofAbbrev! "Brai") char
/-- Check if character is Buginese -/
public def isBuginese (char : Char) : Bool := isScript (Script.ofAbbrev! "Bugi") char
/-- Check if character is Buhid -/
public def isBuhid (char : Char) : Bool := isScript (Script.ofAbbrev! "Buhd") char
/-- Check if character is Canadian_Aboriginal -/
public def isCanadianAboriginal (char : Char) : Bool := isScript (Script.ofAbbrev! "Cans") char
/-- Check if character is Carian -/
public def isCarian (char : Char) : Bool := isScript (Script.ofAbbrev! "Cari") char
/-- Check if character is Caucasian_Albanian -/
public def isCaucasianAlbanian (char : Char) : Bool := isScript (Script.ofAbbrev! "Aghb") char
/-- Check if character is Chakma -/
public def isChakma (char : Char) : Bool := isScript (Script.ofAbbrev! "Cakm") char
/-- Check if character is Cham -/
public def isCham (char : Char) : Bool := isScript (Script.ofAbbrev! "Cham") char
/-- Check if character is Cherokee -/
public def isCherokee (char : Char) : Bool := isScript (Script.ofAbbrev! "Cher") char
/-- Check if character is Chorasmian -/
public def isChorasmian (char : Char) : Bool := isScript (Script.ofAbbrev! "Chrs") char
/-- Check if character is Common -/
public def isCommon (char : Char) : Bool := isScript (Script.ofAbbrev! "Zyyy") char
/-- Check if character is Coptic -/
public def isCoptic (char : Char) : Bool := isScript (Script.ofAbbrev! "Copt") char
/-- Check if character is Cuneiform -/
public def isCuneiform (char : Char) : Bool := isScript (Script.ofAbbrev! "Xsux") char
/-- Check if character is Cypriot -/
public def isCypriot (char : Char) : Bool := isScript (Script.ofAbbrev! "Cprt") char
/-- Check if character is Cypro_Minoan -/
public def isCyproMinoan (char : Char) : Bool := isScript (Script.ofAbbrev! "Cpmn") char
/-- Check if character is Cyrillic -/
public def isCyrillic (char : Char) : Bool := isScript (Script.ofAbbrev! "Cyrl") char
/-- Check if character is Deseret -/
public def isDeseret (char : Char) : Bool := isScript (Script.ofAbbrev! "Dsrt") char
/-- Check if character is Devanagari -/
public def isDevanagari (char : Char) : Bool := isScript (Script.ofAbbrev! "Deva") char
/-- Check if character is Dives_Akuru -/
public def isDivesAkuru (char : Char) : Bool := isScript (Script.ofAbbrev! "Diak") char
/-- Check if character is Dogra -/
public def isDogra (char : Char) : Bool := isScript (Script.ofAbbrev! "Dogr") char
/-- Check if character is Duployan -/
public def isDuployan (char : Char) : Bool := isScript (Script.ofAbbrev! "Dupl") char
/-- Check if character is Egyptian_Hieroglyphs -/
public def isEgyptianHieroglyphs (char : Char) : Bool := isScript (Script.ofAbbrev! "Egyp") char
/-- Check if character is Elbasan -/
public def isElbasan (char : Char) : Bool := isScript (Script.ofAbbrev! "Elba") char
/-- Check if character is Elymaic -/
public def isElymaic (char : Char) : Bool := isScript (Script.ofAbbrev! "Elym") char
/-- Check if character is Ethiopic -/
public def isEthiopic (char : Char) : Bool := isScript (Script.ofAbbrev! "Ethi") char
/-- Check if character is Garay -/
public def isGaray (char : Char) : Bool := isScript (Script.ofAbbrev! "Gara") char
/-- Check if character is Georgian -/
public def isGeorgian (char : Char) : Bool := isScript (Script.ofAbbrev! "Geor") char
/-- Check if character is Glagolitic -/
public def isGlagolitic (char : Char) : Bool := isScript (Script.ofAbbrev! "Glag") char
/-- Check if character is Gothic -/
public def isGothic (char : Char) : Bool := isScript (Script.ofAbbrev! "Goth") char
/-- Check if character is Grantha -/
public def isGrantha (char : Char) : Bool := isScript (Script.ofAbbrev! "Gran") char
/-- Check if character is Greek -/
public def isGreek (char : Char) : Bool := isScript (Script.ofAbbrev! "Grek") char
/-- Check if character is Gujarati -/
public def isGujarati (char : Char) : Bool := isScript (Script.ofAbbrev! "Gujr") char
/-- Check if character is Gunjala_Gondi -/
public def isGunjalaGondi (char : Char) : Bool := isScript (Script.ofAbbrev! "Gong") char
/-- Check if character is Gurmukhi -/
public def isGurmukhi (char : Char) : Bool := isScript (Script.ofAbbrev! "Guru") char
/-- Check if character is Gurung_Khema -/
public def isGurungKhema (char : Char) : Bool := isScript (Script.ofAbbrev! "Gukh") char
/-- Check if character is Han -/
public def isHan (char : Char) : Bool := isScript (Script.ofAbbrev! "Hani") char
/-- Check if character is Hangul -/
public def isHangul (char : Char) : Bool := isScript (Script.ofAbbrev! "Hang") char
/-- Check if character is Hanifi_Rohingya -/
public def isHanifiRohingya (char : Char) : Bool := isScript (Script.ofAbbrev! "Rohg") char
/-- Check if character is Hanunoo -/
public def isHanunoo (char : Char) : Bool := isScript (Script.ofAbbrev! "Hano") char
/-- Check if character is Hatran -/
public def isHatran (char : Char) : Bool := isScript (Script.ofAbbrev! "Hatr") char
/-- Check if character is Hebrew -/
public def isHebrew (char : Char) : Bool := isScript (Script.ofAbbrev! "Hebr") char
/-- Check if character is Hiragana -/
public def isHiragana (char : Char) : Bool := isScript (Script.ofAbbrev! "Hira") char
/-- Check if character is Imperial_Aramaic -/
public def isImperialAramaic (char : Char) : Bool := isScript (Script.ofAbbrev! "Armi") char
/-- Check if character is Inherited -/
public def isInherited (char : Char) : Bool := isScript (Script.ofAbbrev! "Zinh") char
/-- Check if character is Inscriptional_Pahlavi -/
public def isInscriptionalPahlavi (char : Char) : Bool := isScript (Script.ofAbbrev! "Phli") char
/-- Check if character is Inscriptional_Parthian -/
public def isInscriptionalParthian (char : Char) : Bool := isScript (Script.ofAbbrev! "Prti") char
/-- Check if character is Javanese -/
public def isJavanese (char : Char) : Bool := isScript (Script.ofAbbrev! "Java") char
/-- Check if character is Kaithi -/
public def isKaithi (char : Char) : Bool := isScript (Script.ofAbbrev! "Kthi") char
/-- Check if character is Kannada -/
public def isKannada (char : Char) : Bool := isScript (Script.ofAbbrev! "Knda") char
/-- Check if character is Katakana -/
public def isKatakana (char : Char) : Bool := isScript (Script.ofAbbrev! "Kana") char
/-- Check if character is Katakana_Or_Hiragana -/
public def isKatakanaOrHiragana (char : Char) : Bool := isScript (Script.ofAbbrev! "Hrkt") char
/-- Check if character is Kawi -/
public def isKawi (char : Char) : Bool := isScript (Script.ofAbbrev! "Kawi") char
/-- Check if character is Kayah_Li -/
public def isKayahLi (char : Char) : Bool := isScript (Script.ofAbbrev! "Kali") char
/-- Check if character is Kharoshthi -/
public def isKharoshthi (char : Char) : Bool := isScript (Script.ofAbbrev! "Khar") char
/-- Check if character is Khitan_Small_Script -/
public def isKhitanSmallScript (char : Char) : Bool := isScript (Script.ofAbbrev! "Kits") char
/-- Check if character is Khmer -/
public def isKhmer (char : Char) : Bool := isScript (Script.ofAbbrev! "Khmr") char
/-- Check if character is Khojki -/
public def isKhojki (char : Char) : Bool := isScript (Script.ofAbbrev! "Khoj") char
/-- Check if character is Khudawadi -/
public def isKhudawadi (char : Char) : Bool := isScript (Script.ofAbbrev! "Sind") char
/-- Check if character is Kirat_Rai -/
public def isKiratRai (char : Char) : Bool := isScript (Script.ofAbbrev! "Krai") char
/-- Check if character is Lao -/
public def isLao (char : Char) : Bool := isScript (Script.ofAbbrev! "Laoo") char
/-- Check if character is Latin -/
public def isLatin (char : Char) : Bool := isScript (Script.ofAbbrev! "Latn") char
/-- Check if character is Lepcha -/
public def isLepcha (char : Char) : Bool := isScript (Script.ofAbbrev! "Lepc") char
/-- Check if character is Limbu -/
public def isLimbu (char : Char) : Bool := isScript (Script.ofAbbrev! "Limb") char
/-- Check if character is Linear_A -/
public def isLinearA (char : Char) : Bool := isScript (Script.ofAbbrev! "Lina") char
/-- Check if character is Linear_B -/
public def isLinearB (char : Char) : Bool := isScript (Script.ofAbbrev! "Linb") char
/-- Check if character is Lisu -/
public def isLisu (char : Char) : Bool := isScript (Script.ofAbbrev! "Lisu") char
/-- Check if character is Lycian -/
public def isLycian (char : Char) : Bool := isScript (Script.ofAbbrev! "Lyci") char
/-- Check if character is Lydian -/
public def isLydian (char : Char) : Bool := isScript (Script.ofAbbrev! "Lydi") char
/-- Check if character is Mahajani -/
public def isMahajani (char : Char) : Bool := isScript (Script.ofAbbrev! "Mahj") char
/-- Check if character is Makasar -/
public def isMakasar (char : Char) : Bool := isScript (Script.ofAbbrev! "Maka") char
/-- Check if character is Malayalam -/
public def isMalayalam (char : Char) : Bool := isScript (Script.ofAbbrev! "Mlym") char
/-- Check if character is Mandaic -/
public def isMandaic (char : Char) : Bool := isScript (Script.ofAbbrev! "Mand") char
/-- Check if character is Manichaean -/
public def isManichaean (char : Char) : Bool := isScript (Script.ofAbbrev! "Mani") char
/-- Check if character is Marchen -/
public def isMarchen (char : Char) : Bool := isScript (Script.ofAbbrev! "Marc") char
/-- Check if character is Masaram_Gondi -/
public def isMasaramGondi (char : Char) : Bool := isScript (Script.ofAbbrev! "Gonm") char
/-- Check if character is Medefaidrin -/
public def isMedefaidrin (char : Char) : Bool := isScript (Script.ofAbbrev! "Medf") char
/-- Check if character is Meetei_Mayek -/
public def isMeeteiMayek (char : Char) : Bool := isScript (Script.ofAbbrev! "Mtei") char
/-- Check if character is Mende_Kikakui -/
public def isMendeKikakui (char : Char) : Bool := isScript (Script.ofAbbrev! "Mend") char
/-- Check if character is Meroitic_Cursive -/
public def isMeroiticCursive (char : Char) : Bool := isScript (Script.ofAbbrev! "Merc") char
/-- Check if character is Meroitic_Hieroglyphs -/
public def isMeroiticHieroglyphs (char : Char) : Bool := isScript (Script.ofAbbrev! "Mero") char
/-- Check if character is Miao -/
public def isMiao (char : Char) : Bool := isScript (Script.ofAbbrev! "Plrd") char
/-- Check if character is Modi -/
public def isModi (char : Char) : Bool := isScript (Script.ofAbbrev! "Modi") char
/-- Check if character is Mongolian -/
public def isMongolian (char : Char) : Bool := isScript (Script.ofAbbrev! "Mong") char
/-- Check if character is Mro -/
public def isMro (char : Char) : Bool := isScript (Script.ofAbbrev! "Mroo") char
/-- Check if character is Multani -/
public def isMultani (char : Char) : Bool := isScript (Script.ofAbbrev! "Mult") char
/-- Check if character is Myanmar -/
public def isMyanmar (char : Char) : Bool := isScript (Script.ofAbbrev! "Mymr") char
/-- Check if character is Nabataean -/
public def isNabataean (char : Char) : Bool := isScript (Script.ofAbbrev! "Nbat") char
/-- Check if character is Nag_Mundari -/
public def isNagMundari (char : Char) : Bool := isScript (Script.ofAbbrev! "Nagm") char
/-- Check if character is Nandinagari -/
public def isNandinagari (char : Char) : Bool := isScript (Script.ofAbbrev! "Nand") char
/-- Check if character is New_Tai_Lue -/
public def isNewTaiLue (char : Char) : Bool := isScript (Script.ofAbbrev! "Talu") char
/-- Check if character is Newa -/
public def isNewa (char : Char) : Bool := isScript (Script.ofAbbrev! "Newa") char
/-- Check if character is Nko -/
public def isNko (char : Char) : Bool := isScript (Script.ofAbbrev! "Nkoo") char
/-- Check if character is Nushu -/
public def isNushu (char : Char) : Bool := isScript (Script.ofAbbrev! "Nshu") char
/-- Check if character is Nyiakeng_Puachue_Hmong -/
public def isNyiakengPuachueHmong (char : Char) : Bool := isScript (Script.ofAbbrev! "Hmnp") char
/-- Check if character is Ogham -/
public def isOgham (char : Char) : Bool := isScript (Script.ofAbbrev! "Ogam") char
/-- Check if character is Ol_Chiki -/
public def isOlChiki (char : Char) : Bool := isScript (Script.ofAbbrev! "Olck") char
/-- Check if character is Ol_Onal -/
public def isOlOnal (char : Char) : Bool := isScript (Script.ofAbbrev! "Onao") char
/-- Check if character is Old_Hungarian -/
public def isOldHungarian (char : Char) : Bool := isScript (Script.ofAbbrev! "Hung") char
/-- Check if character is Old_Italic -/
public def isOldItalic (char : Char) : Bool := isScript (Script.ofAbbrev! "Ital") char
/-- Check if character is Old_North_Arabian -/
public def isOldNorthArabian (char : Char) : Bool := isScript (Script.ofAbbrev! "Narb") char
/-- Check if character is Old_Permic -/
public def isOldPermic (char : Char) : Bool := isScript (Script.ofAbbrev! "Perm") char
/-- Check if character is Old_Persian -/
public def isOldPersian (char : Char) : Bool := isScript (Script.ofAbbrev! "Xpeo") char
/-- Check if character is Old_Sogdian -/
public def isOldSogdian (char : Char) : Bool := isScript (Script.ofAbbrev! "Sogo") char
/-- Check if character is Old_South_Arabian -/
public def isOldSouthArabian (char : Char) : Bool := isScript (Script.ofAbbrev! "Sarb") char
/-- Check if character is Old_Turkic -/
public def isOldTurkic (char : Char) : Bool := isScript (Script.ofAbbrev! "Orkh") char
/-- Check if character is Old_Uyghur -/
public def isOldUyghur (char : Char) : Bool := isScript (Script.ofAbbrev! "Ougr") char
/-- Check if character is Oriya -/
public def isOriya (char : Char) : Bool := isScript (Script.ofAbbrev! "Orya") char
/-- Check if character is Osage -/
public def isOsage (char : Char) : Bool := isScript (Script.ofAbbrev! "Osge") char
/-- Check if character is Osmanya -/
public def isOsmanya (char : Char) : Bool := isScript (Script.ofAbbrev! "Osma") char
/-- Check if character is Pahawh_Hmong -/
public def isPahawhHmong (char : Char) : Bool := isScript (Script.ofAbbrev! "Hmng") char
/-- Check if character is Palmyrene -/
public def isPalmyrene (char : Char) : Bool := isScript (Script.ofAbbrev! "Palm") char
/-- Check if character is Pau_Cin_Hau -/
public def isPauCinHau (char : Char) : Bool := isScript (Script.ofAbbrev! "Pauc") char
/-- Check if character is Phags_Pa -/
public def isPhagsPa (char : Char) : Bool := isScript (Script.ofAbbrev! "Phag") char
/-- Check if character is Phoenician -/
public def isPhoenician (char : Char) : Bool := isScript (Script.ofAbbrev! "Phnx") char
/-- Check if character is Psalter_Pahlavi -/
public def isPsalterPahlavi (char : Char) : Bool := isScript (Script.ofAbbrev! "Phlp") char
/-- Check if character is Rejang -/
public def isRejang (char : Char) : Bool := isScript (Script.ofAbbrev! "Rjng") char
/-- Check if character is Runic -/
public def isRunic (char : Char) : Bool := isScript (Script.ofAbbrev! "Runr") char
/-- Check if character is Samaritan -/
public def isSamaritan (char : Char) : Bool := isScript (Script.ofAbbrev! "Samr") char
/-- Check if character is Saurashtra -/
public def isSaurashtra (char : Char) : Bool := isScript (Script.ofAbbrev! "Saur") char
/-- Check if character is Sharada -/
public def isSharada (char : Char) : Bool := isScript (Script.ofAbbrev! "Shrd") char
/-- Check if character is Shavian -/
public def isShavian (char : Char) : Bool := isScript (Script.ofAbbrev! "Shaw") char
/-- Check if character is Siddham -/
public def isSiddham (char : Char) : Bool := isScript (Script.ofAbbrev! "Sidd") char
/-- Check if character is Sidetic -/
public def isSidetic (char : Char) : Bool := isScript (Script.ofAbbrev! "Sidt") char
/-- Check if character is SignWriting -/
public def isSignWriting (char : Char) : Bool := isScript (Script.ofAbbrev! "Sgnw") char
/-- Check if character is Sinhala -/
public def isSinhala (char : Char) : Bool := isScript (Script.ofAbbrev! "Sinh") char
/-- Check if character is Sogdian -/
public def isSogdian (char : Char) : Bool := isScript (Script.ofAbbrev! "Sogd") char
/-- Check if character is Sora_Sompeng -/
public def isSoraSompeng (char : Char) : Bool := isScript (Script.ofAbbrev! "Sora") char
/-- Check if character is Soyombo -/
public def isSoyombo (char : Char) : Bool := isScript (Script.ofAbbrev! "Soyo") char
/-- Check if character is Sundanese -/
public def isSundanese (char : Char) : Bool := isScript (Script.ofAbbrev! "Sund") char
/-- Check if character is Sunuwar -/
public def isSunuwar (char : Char) : Bool := isScript (Script.ofAbbrev! "Sunu") char
/-- Check if character is Syloti_Nagri -/
public def isSylotiNagri (char : Char) : Bool := isScript (Script.ofAbbrev! "Sylo") char
/-- Check if character is Syriac -/
public def isSyriac (char : Char) : Bool := isScript (Script.ofAbbrev! "Syrc") char
/-- Check if character is Tagalog -/
public def isTagalog (char : Char) : Bool := isScript (Script.ofAbbrev! "Tglg") char
/-- Check if character is Tagbanwa -/
public def isTagbanwa (char : Char) : Bool := isScript (Script.ofAbbrev! "Tagb") char
/-- Check if character is Tai_Le -/
public def isTaiLe (char : Char) : Bool := isScript (Script.ofAbbrev! "Tale") char
/-- Check if character is Tai_Tham -/
public def isTaiTham (char : Char) : Bool := isScript (Script.ofAbbrev! "Lana") char
/-- Check if character is Tai_Viet -/
public def isTaiViet (char : Char) : Bool := isScript (Script.ofAbbrev! "Tavt") char
/-- Check if character is Tai_Yo -/
public def isTaiYo (char : Char) : Bool := isScript (Script.ofAbbrev! "Tayo") char
/-- Check if character is Takri -/
public def isTakri (char : Char) : Bool := isScript (Script.ofAbbrev! "Takr") char
/-- Check if character is Tamil -/
public def isTamil (char : Char) : Bool := isScript (Script.ofAbbrev! "Taml") char
/-- Check if character is Tangsa -/
public def isTangsa (char : Char) : Bool := isScript (Script.ofAbbrev! "Tnsa") char
/-- Check if character is Tangut -/
public def isTangut (char : Char) : Bool := isScript (Script.ofAbbrev! "Tang") char
/-- Check if character is Telugu -/
public def isTelugu (char : Char) : Bool := isScript (Script.ofAbbrev! "Telu") char
/-- Check if character is Thaana -/
public def isThaana (char : Char) : Bool := isScript (Script.ofAbbrev! "Thaa") char
/-- Check if character is Thai -/
public def isThai (char : Char) : Bool := isScript (Script.ofAbbrev! "Thai") char
/-- Check if character is Tibetan -/
public def isTibetan (char : Char) : Bool := isScript (Script.ofAbbrev! "Tibt") char
/-- Check if character is Tifinagh -/
public def isTifinagh (char : Char) : Bool := isScript (Script.ofAbbrev! "Tfng") char
/-- Check if character is Tirhuta -/
public def isTirhuta (char : Char) : Bool := isScript (Script.ofAbbrev! "Tirh") char
/-- Check if character is Todhri -/
public def isTodhri (char : Char) : Bool := isScript (Script.ofAbbrev! "Todr") char
/-- Check if character is Tolong_Siki -/
public def isTolongSiki (char : Char) : Bool := isScript (Script.ofAbbrev! "Tols") char
/-- Check if character is Toto -/
public def isToto (char : Char) : Bool := isScript (Script.ofAbbrev! "Toto") char
/-- Check if character is Tulu_Tigalari -/
public def isTuluTigalari (char : Char) : Bool := isScript (Script.ofAbbrev! "Tutg") char
/-- Check if character is Ugaritic -/
public def isUgaritic (char : Char) : Bool := isScript (Script.ofAbbrev! "Ugar") char
/-- Check if character is Unknown -/
public def isUnknown (char : Char) : Bool := isScript (Script.ofAbbrev! "Zzzz") char
/-- Check if character is Vai -/
public def isVai (char : Char) : Bool := isScript (Script.ofAbbrev! "Vaii") char
/-- Check if character is Vithkuqi -/
public def isVithkuqi (char : Char) : Bool := isScript (Script.ofAbbrev! "Vith") char
/-- Check if character is Wancho -/
public def isWancho (char : Char) : Bool := isScript (Script.ofAbbrev! "Wcho") char
/-- Check if character is Warang_Citi -/
public def isWarangCiti (char : Char) : Bool := isScript (Script.ofAbbrev! "Wara") char
/-- Check if character is Yezidi -/
public def isYezidi (char : Char) : Bool := isScript (Script.ofAbbrev! "Yezi") char
/-- Check if character is Yi -/
public def isYi (char : Char) : Bool := isScript (Script.ofAbbrev! "Yiii") char
/-- Check if character is Zanabazar_Square -/
public def isZanabazarSquare (char : Char) : Bool := isScript (Script.ofAbbrev! "Zanb") char


/-!
  ## Bidirectional Properties ##
-/

/-- Get character bidirectional class

  Unicode property: `Bidi_Class` -/
@[inline]
public def getBidiClass (char : Char) : BidiClass := lookupBidiClass char.val

/-- Check if bidirectional mirrored character

  Unicode property: `Bidi_Mirrored` -/
@[inline]
public def isBidiMirrored (char : Char) : Bool := lookupBidiMirrored char.val

/-- Check if bidirectional control character

  Unicode property: `Bidi_Control` -/
@[inline]
public def isBidiControl (char : Char) : Bool :=
  -- Extracted from `PropList.txt`
  char.val == 0x061C
  || char.val <= 0x200F && char.val >= 0x200E
  || char.val <= 0x202E && char.val >= 0x202A
  || char.val <= 0x2069 && char.val >= 0x2066

/-!
  ## General Category ##
-/

/-- Get character general category

  *Caveat*: This function never returns a derived general category. Use
  `Unicode.isInGeneralCategory` to check whether a character belongs to a
  general category (derived or not).

  Unicode property: `General_Category` -/
@[inline]
public def getGC (char : Char) : GC :=
  -- ASCII shortcut
  if h : char.toNat < table.size then
    table[char.toNat]
  else
    lookupGC char.val
where
  table : Array GC :=
    #[.Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc,
      .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc,
      .Zs, .Po, .Po, .Po, .Sc, .Po, .Po, .Po, .Ps, .Po, .Po, .Sm, .Po, .Pd, .Po, .Po,
      .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Po, .Po, .Sm, .Sm, .Sm, .Po,
      .Po, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu,
      .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Ps, .Po, .Po, .Sk, .Pc,
      .Sk, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll,
      .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ps, .Sm, .Po, .Sm, .Cc]

public instance : Membership Char GC where
  mem cat char := getGC char ⊆ cat

public instance (char : Char) (cat : GC) : Decidable (char ∈ cat) := inferInstanceAs (Decidable (_ ⊆ _))

namespace GeneralCategory

/-- Check if letter character (`L`)

  This is a derived category (`L = Lu | Ll | Lt | Lm | Lo`).

  Unicode Property: `General_Category=L` -/
public abbrev isLetter (char : Char) : Bool := char ∈ Unicode.GC.L

/-- Check if lowercase letter character (`Ll`)

  Unicode Property: `General_Category=Ll` -/
public abbrev isLowercaseLetter (char : Char) : Bool := char ∈ Unicode.GC.Ll

/-- Check if titlecase letter character (`Lt`)

  Unicode Property: `General_Category=Lt` -/
public abbrev isTitlecaseLetter (char : Char) : Bool := char ∈ Unicode.GC.Lt

/-- Check if uppercase letter character (`Lu`)

  Unicode Property: `General_Category=Lu` -/
public abbrev isUppercaseLetter (char : Char) : Bool := char ∈ Unicode.GC.Lu

/-- Check if cased letter character (`LC`)

  This is a derived category (`L = Lu | Ll | Lt`).

  Unicode Property: `General_Category=LC` -/
public abbrev isCasedLetter (char : Char) : Bool := char ∈ Unicode.GC.LC

/-- Check if modifier letter character (`Lm`)

  Unicode Property: `General_Category=Lm`-/
public abbrev isModifierLetter (char : Char) : Bool := char ∈ Unicode.GC.Lm

/-- Check if other letter character (`Lo`)

  Unicode Property: `General_Category=Lo`-/
public abbrev isOtherLetter (char : Char) : Bool := char ∈ Unicode.GC.Lo

/-- Check if mark character (`M`)

  This is a derived category (`M = Mn | Mc | Me`).

  Unicode Property: `General_Category=M` -/
public abbrev isMark (char : Char) : Bool := char ∈ Unicode.GC.M

/-- Check if nonspacing combining mark character (`Mn`)

  Unicode Property: `General_Category=Mn` -/
public abbrev isNonspacingMark (char : Char) : Bool := char ∈ Unicode.GC.Mn

/-- Check if spacing combining mark character (`Mc`)

  Unicode Property: `General_Category=Mc` -/
public abbrev isSpacingMark (char : Char) : Bool := char ∈ Unicode.GC.Mc

/-- Check if enclosing combining mark character (`Me`)

  Unicode Property: `General_Category=Me` -/
public abbrev isEnclosingMark (char : Char) : Bool := char ∈ Unicode.GC.Me

/-- Check if number character (`N`)

  This is a derived category (`N = Nd | Nl | No`).

  Unicode Property: `General_Category=N` -/
public abbrev isNumber (char : Char) : Bool := char ∈ Unicode.GC.N

/-- Check if decimal number character (`Nd`)

  Unicode Property: `General_Category=Nd` -/
public abbrev isDecimalNumber (char : Char) : Bool := char ∈ Unicode.GC.Nd

/-- Check if letter number character (`Nl`)

  Unicode Property: `General_Category=Nl` -/
public abbrev isLetterNumber (char : Char) : Bool := char ∈ Unicode.GC.Nl

/-- Check if other number character (`No`)

  Unicode Property: `General_Category=No` -/
public abbrev isOtherNumber (char : Char) : Bool := char ∈ Unicode.GC.No

/-- Check if punctuation character (`P`)

  This is a derived category (`P = Pc | Pd | Ps | Pe | Pi | Pf | Po`).

  Unicode Property: `General_Category=P` -/
public abbrev isPunctuation (char : Char) : Bool := char ∈ Unicode.GC.P

/-- Check if connector punctuation character (`Pc`)

  Unicode Property: `General_Category=Pc` -/
public abbrev isConnectorPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pc

/-- Check if dash punctuation character (`Pd`)

  Unicode Property: `General_Category=Pd` -/
public abbrev isDashPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pd

/-- Check if grouping punctuation character (`PG`)

  This is a derived category (`PG = Ps | Pe`).

  Unicode Property: `General_Category=PG` -/
public abbrev isGroupPunctuation (char : Char) : Bool := char ∈ Unicode.GC.PG

/-- Check if open punctuation character (`Ps`)

  Unicode Property: `General_Category=Ps` -/
public abbrev isOpenPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Ps

/-- Check if close punctuation character (`Pe`)

  Unicode Property: `General_Category=Pe` -/
public abbrev isClosePunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pe

/-- Check if quoting punctuation character (`PQ`)

  This is a derived category (`PQ = Pi | Pf`).

  Unicode Property: `General_Category=PQ` -/
public abbrev isQuotePunctuation (char : Char) : Bool := char ∈ Unicode.GC.PQ

/-- Check if initial punctuation character (`Pi`)

  Unicode Property: `General_Category=Pi` -/
public abbrev isInitialPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pi

/-- Check if initial punctuation character (`Pf`)

  Unicode Property: `General_Category=Pf` -/
public abbrev isFinalPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pf

/-- Check if other punctuation character (`Po`)

  Unicode Property: `General_Category=Po` -/
public abbrev isOtherPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Po

/-- Check if symbol character (`S`)

  This is a derived category (`S = Sm | Sc | Sk | So`).

  Unicode Property: `General_Category=S` -/
public abbrev isSymbol (char : Char) : Bool := char ∈ Unicode.GC.S

/-- Check if math symbol character (`Sm`)

  Unicode Property: `General_Category=Sm` -/
public abbrev isMathSymbol (char : Char) : Bool := char ∈ Unicode.GC.Sm

/-- Check if currency symbol character (`Sc`)

  Unicode Property: `General_Category=Sc` -/
public abbrev isCurrencySymbol (char : Char) : Bool := char ∈ Unicode.GC.Sc

/-- Check if modifier symbol character (`Sk`)

  Unicode Property: `General_Category=Sk` -/
public abbrev isModifierSymbol (char : Char) : Bool := char ∈ Unicode.GC.Sk

/-- Check if other symbol character (`So`)

  Unicode Property: `General_Category=So` -/
public abbrev isOtherSymbol (char : Char) : Bool := char ∈ Unicode.GC.So

/-- Check if separator character (`Z`)

  This is a derived property (`Z = Zs | Zl | Zp`).

  Unicode Property: `General_Category=Z` -/
public abbrev isSeparator (char : Char) : Bool := char ∈ Unicode.GC.Z

/-- Check if space separator character (`Zs`)

  Unicode Property: `General_Category=Zs` -/
public abbrev isSpaceSeparator (char : Char) : Bool := char ∈ Unicode.GC.Zs

/-- Check if line separator character (`Zl`)

  Unicode Property: `General_Category=Zl` -/
public abbrev isLineSeparator (char : Char) : Bool := char ∈ Unicode.GC.Zl

/-- Check if paragraph separator character (`Zp`)

  Unicode Property: `General_Category=Zp` -/
public abbrev isParagraphSeparator (char : Char) : Bool := char ∈ Unicode.GC.Zp

/-- Check if other character (`C`)

  This is a derived category (`C = Cc | Cf | Cs | Co | Cn`).

  Unicode Property: `General_Category=C` -/
public abbrev isOther (char : Char) : Bool := char ∈ Unicode.GC.C

/-- Check if control character (`Cc`)

  Unicode Property: `General_Category=Cc` -/
public abbrev isControl (char : Char) : Bool := char ∈ Unicode.GC.Cc

/-- Check if format character (`Cf`)

  Unicode Property: `General_Category=Cf` -/
public abbrev isFormat (char : Char) : Bool := char ∈ Unicode.GC.Cf

/-- Check if surrogate character (`Cs`)

  Does not actually occur since Lean does not regard surrogate code points as characters.

  Unicode Property: `General_Category=Cs` -/
public abbrev isSurrogate (char : Char) : Bool := char ∈ Unicode.GC.Cs

/-- Check if private use character (`Co`)

  Unicode Property: `General_Category=Co` -/
public abbrev isPrivateUse (char : Char) : Bool := char ∈ Unicode.GC.Co

/-- Check if unassigned character (`Cn`)

  Unicode Property: `General_Category=Cn` -/
public abbrev isUnassigned (char : Char) : Bool := char ∈ Unicode.GC.Cn

end GeneralCategory

/-!
  ## Case Type and Mapping ##
-/

/-- Check if lowercase letter character

  Generated by `General_Category=Ll | Other_Lowercase`.

  Unicode property: `Lowercase` -/
@[inline]
public def isLowercase (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'a' ≤ char && char ≤ 'z'
  else
    lookupLowercase char.val

/-- Check if uppercase letter character

  Generated by `General_Category=Lu | Other_Uppercase`.

  Unicode property: `Uppercase` -/
@[inline]
public def isUppercase (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'A' ≤ char && char ≤ 'Z'
  else
    lookupUppercase char.val

/-- Check if cased letter character

  Generated by `General_Category=LC | Other_Lowercase | Other_Uppercase`.

  Unicode property: `Cased` -/
@[inline]
public def isCased (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'A' ≤ char && char ≤ 'Z' || 'a' ≤ char && char ≤ 'z'
  else
    lookupCased char.val

/-- Check if character is ignorable for casing purposes

  Generated from general categories `Lm`, `Mn`, `Me`, `Sk`, `Cf`, and word
  break properties `MidLetter`, `MidNumLet`, `Single_Quote`.

  Unicode property: `Case_Ignorable` -/
@[inline]
public def isCaseIgnorable (char : Char) : Bool :=
  char ∈ Unicode.GC.Lm ||| GC.Mn ||| GC.Sk ||| GC.Cf || other.elem char.val
where
  /-- Auxiliary data for `isCaseIgnorable`

    Extracted from UCD `auxiliary/WordBreakProperty.txt`. -/
  other : List UInt32 := [
    0x0027, -- Single_Quote APOSTROPHE
    0x002E, -- MidNumLet    FULL STOP
    0x003A, -- MidLetter    COLON
    0x00B7, -- MidLetter    MIDDLE DOT
    0x0387, -- MidLetter    GREEK ANO TELEIA
    0x055F, -- MidLetter    ARMENIAN ABBREVIATION MARK
    0x05F4, -- MidLetter    HEBREW PUNCTUATION GERSHAYIM
    0x2018, -- MidNumLet    LEFT SINGLE QUOTATION MARK
    0x2019, -- MidNumLet    RIGHT SINGLE QUOTATION MARK
    0x2027, -- MidLetter    HYPHENATION POINT
    0x2024, -- MidNumLet    ONE DOT LEADER
    0xFE13, -- MidLetter    PRESENTATION FORM FOR VERTICAL COLON
    0xFE55, -- MidLetter    SMALL COLON
    0xFE52, -- MidNumLet    SMALL FULL STOP
    0xFF07, -- MidNumLet    FULLWIDTH APOSTROPHE
    0xFF0E, -- MidNumLet    FULLWIDTH FULL STOP
    0xFF1A] -- MidLetter    FULLWIDTH COLON

/-- Map character to lowercase

  This function does not handle the case where the lowercase mapping would
  consist of more than one character.

  Unicode property: `Simple_Lowercase_Mapping` -/
@[inline]
public def getLowerChar (char : Char) : Char :=
  -- ASCII shortcut
  if char.val < 0x80 then
    if 'A' ≤ char && char ≤ 'Z' then
      Char.ofNat (char.val + 0x20).toNat
    else
      char
  else
    match lookupCaseMapping char.val with
    | (_, lc, _) => Char.ofNat lc.toNat

/-- Map character to uppercase

  This function does not handle the case where the uppercase mapping would
  consist of more than one character.

  Unicode property: `Simple_Uppercase_Mapping` -/
@[inline]
public def getUpperChar (char : Char) : Char :=
  if char.val < 0x80 then
    if 'a' ≤ char && char ≤ 'z' then
      Char.ofNat (char.val - 0x20).toNat
    else
      char
  else
    match lookupCaseMapping char.val with
    | (uc, _, _) => Char.ofNat uc.toNat

/-- Map character to titlecase

  This function does not handle the case where the titlecase mapping would
  consist of more than one character.

  Unicode property: `Simple_Titlecase_Mapping` -/
@[inline]
public def getTitleChar (char : Char) : Char :=
  if char.val < 0x80 then
    if 'a' ≤ char && char ≤ 'z' then
      Char.ofNat (char.val - 0x20).toNat
    else
      char
  else
    match lookupCaseMapping char.val with
    | (_, _, tc) => Char.ofNat tc.toNat

/-!
  ## Decomposition Type and Mapping ##
-/

/-- Get canonical combining class of character

  Unicode property: `Canonical_Combining_Class`
-/
public def getCanonicalCombiningClass (char : Char) : Nat :=
  -- ASCII shortcut
  if char.val < 0x80 then
    0
  else
    lookupCanonicalCombiningClass char.val

/-- Get canonical decomposition of character (`NFD`)

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type=Canonical` -/
public def getCanonicalDecomposition (char : Char) : String :=
  -- ASCII shortcut
  if char.val < 0x80 then char.toString else
    String.ofList <| (lookupCanonicalDecompositionMapping char.val).map fun c => Char.ofNat c.toNat

/-- Get decomposition mapping of a character

  This is used in normalization to canonical decomposition (`NFD`) and compatibility
  decomposition (`NFKD`).

  Unicode properties:
  `Decomposition_Type`
  `Decomposition_Mapping` -/
public def getDecompositionMapping? (char : Char) : Option DecompositionMapping :=
  -- ASCII shortcut
  if char.val < 0x80 then
    none
  else
    lookupDecompositionMapping? char.val

/-!
  ## Numeric Type and Value ##
-/

/-- Check if character represents a numerical value

  Unicode property: `Numeric_Type=Numeric` -/
@[inline]
public def isNumeric (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char >= '0' && char <= '9'
  else
    match lookupNumericValue char.val with
    | some _ => true
    | _ => otherNumeric.elem char.val
where
  -- Extracted
  otherNumeric := #[
    0x3405, 0x3483, 0x382A, 0x3B4D, 0x4E00, 0x4E03, 0x4E07, 0x4E09, 0x4E5D, 0x4E8C,
    0x4E94, 0x4E96, 0x4EBF, 0x4EC0, 0x4EDF, 0x4EE8, 0x4F0D, 0x4F70, 0x5104, 0x5146,
    0x5169, 0x516B, 0x516D, 0x5341, 0x5343, 0x5344, 0x5345, 0x534C, 0x53C1, 0x53C2,
    0x53C3, 0x53C4, 0x56DB, 0x58F1, 0x58F9, 0x5E7A, 0x5EFE, 0x5EFF, 0x5F0C, 0x5F0D,
    0x5F0E, 0x5F10, 0x62FE, 0x634C, 0x67D2, 0x6F06, 0x7396, 0x767E, 0x8086, 0x842C,
    0x8CAE, 0x8CB3, 0x8D30, 0x9621, 0x9646, 0x964C, 0x9678, 0x96F6, 0xF96B, 0xF973,
    0xF978, 0xF9B2, 0xF9D1, 0xF9D3, 0xF9FD, 0x20001, 0x20064, 0x200E2, 0x20121, 0x2092A,
    0x20983, 0x2098C, 0x2099C, 0x20AEA, 0x20AFD, 0x20B19, 0x22390, 0x22998, 0x23B1B, 0x2626D,
    0x2F890]

/-- Check if character represents a digit in base 10

  Unicode property: `Numeric_Type=Digit` -/
@[inline]
public def isDigit (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char >= '0' && char <= '9'
  else
    match lookupNumericValue char.val with
    | some (.decimal _) => true
    | some (.digit _) => true
    | _ => false

/-- Get value of digit

  Unicode properties:
    `Numeric_Type=Digit`
    `Numeric_Value` -/
@[inline]
public def getDigit? (char : Char) : Option (Fin 10) :=
  -- ASCII shortcut
  if char.val < 0x80 then
    if char.toNat < '0'.toNat then
      none
    else
      let n := char.toNat - '0'.toNat
      if h : n < 10 then
        some ⟨n, h⟩
      else
        none
  else
    match lookupNumericValue char.val with
    | some (.decimal value) => some value
    | some (.digit value) => some value
    | _ => none

/-- Check if character represents a decimal digit

  For this property, a character must be part of a contiguous sequence
  representing the ten decimal digits in order from 0 to 9.

  Unicode property: `Numeric_Type=Decimal` -/
@[inline]
public def isDecimal (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char >= '0' && char <= '9'
  else
    match lookupNumericValue char.val with
    | some (.decimal _) => true
    | _ => false

/-- Get decimal digit range

  If the character is part of a contiguous sequence representing the ten
  decimal digits in order from 0 to 9, this function returns the first and
  last characters from this range.

  Unicode properties:
    `Numeric_Type=Decimal`
    `Numeric_Value` -/
@[inline]
public def getDecimalRange? (char : Char) : Option (Char × Char) :=
  -- ASCII shortcut
  if char.val < 0x80 then
    if char >= '0' && char <= '9' then
      some ('0', '9')
    else
      none
  else
    match lookupNumericValue char.val with
    | some (.decimal value) =>
      let first := char.toNat - value.val
      some (Char.ofNat first, Char.ofNat (first + 9))
    | _ => none

/-- Check if character represents a hexadecimal digit

  Unicode property: `Hex_Digit` -/
@[inline]
public def isHexDigit (char : Char) : Bool :=
  -- Extracted from `PropList.txt`
  char.val <= 0x0039 && char.val >= 0x0030 || -- [10] DIGIT ZERO..DIGIT NINE
  char.val <= 0x0046 && char.val >= 0x0041 || --  [6] LATIN CAPITAL LETTER A..LATIN CAPITAL LETTER F
  char.val <= 0x0066 && char.val >= 0x0061 || --  [6] LATIN SMALL LETTER A..LATIN SMALL LETTER F
  char.val <= 0xFF19 && char.val >= 0xFF10 || -- [10] FULLWIDTH DIGIT ZERO..FULLWIDTH DIGIT NINE
  char.val <= 0xFF26 && char.val >= 0xFF21 || --  [6] FULLWIDTH LATIN CAPITAL LETTER A..FULLWIDTH LATIN CAPITAL LETTER F
  char.val <= 0xFF46 && char.val >= 0xFF41    --  [6] FULLWIDTH LATIN SMALL LETTER A..FULLWIDTH LATIN SMALL LETTER F

/-- Get value of a hexadecimal digit

  Unicode property: `Hex_Digit` -/
@[inline]
public def getHexDigit? (char : Char) : Option (Fin 16) :=
  if char.toNat < 0x30 then
    none
  else
    let n := if char.toNat < 0xFF10 then char.toNat - 0x0030 else char.toNat - 0xFF10
    if h : n < 10 then
      some ⟨n, Nat.lt_trans h (by decide)⟩
    else if n >= 17 then
      let n := n - 7
      if h : n < 16 then
        some ⟨n, h⟩
      else if n >= 32 then
        if h : n - 32 < 16 then
          some ⟨n - 32, h⟩
        else
          none
      else
        none
    else
      none


/-!
  ## Other Properties ##
-/

/-- Check if noncharacter

  Unicode property: `Noncharacter_Code_Point`
-/
@[inline]
public def isNoncharacterCodePoint (char : Char) : Bool :=
  lookupNoncharacterCodePoint char.val

/-- Check if ignorable character

  Unicode property: `Default_Ignorable_Code_Point`
-/
@[inline]
public def isDefaultIgnorableCodePoint (char : Char) : Bool :=
  lookupDefaultIgnorableCodePoint char.val

/-- Check if white space character

  Unicode property: `White_Space`
-/
@[inline]
public def isWhiteSpace (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char == ' ' || char >= '\t' && char <= '\r'
  else
    GeneralCategory.isSeparator char

/-- Check if mathematical symbol character

  Generated by `GeneralCategory=Sm | Other_Math`.

  Unicode property: `Math` -/
@[inline]
public def isMath (char : Char) : Bool := lookupMath char.val

/-- Check if alphabetic character

  Generated by `GeneralCategory=L | GeneralCategory=Nl | Other_Alphabetic`.

  Unicode property: `Alphabetic` -/
@[inline]
public def isAlphabetic (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'A' ≤ char && char ≤ 'Z' || 'a' ≤ char && char ≤ 'z'
  else
    lookupAlphabetic char.val

@[inherit_doc isAlphabetic]
public abbrev isAlpha := isAlphabetic


/-!
  ## Extended Properties ##
-/

/-- Check if character is an identifier start character

  Unicode property: `ID_Start` -/
@[inline]
public def isIDStart (char : Char) : Bool := lookupIDStart char.val

/-- Check if character is an identifier continue character

  Unicode property: `ID_Continue` -/
@[inline]
public def isIDContinue (char : Char) : Bool := lookupIDContinue char.val

/-- Check if character is an identifier start character

  Unicode property: `XID_Start` -/
@[inline]
public def isXIDStart (char : Char) : Bool := lookupXIDStart char.val

/-- Check if character is an identifier continue character

  Unicode property: `XID_Continue` -/
@[inline]
public def isXIDContinue (char : Char) : Bool := lookupXIDContinue char.val

/-- Check if character is a dash character

  Unicode property: `Dash` -/
@[inline]
public def isDash (char : Char) : Bool := lookupDash char.val

/-- Check if character is a hyphen character

  Unicode property: `Hyphen` -/
@[inline]
public def isHyphen (char : Char) : Bool := lookupHyphen char.val

/-- Check if character is a quotation mark character

  Unicode property: `Quotation_Mark` -/
@[inline]
public def isQuotationMark (char : Char) : Bool := lookupQuotationMark char.val

/-- Check if character is a terminal punctuation character

  Unicode property: `Terminal_Punctuation` -/
@[inline]
public def isTerminalPunctuation (char : Char) : Bool := lookupTerminalPunctuation char.val

/-- Check if character is an extender character

  Unicode property: `Extender` -/
@[inline]
public def isExtender (char : Char) : Bool := lookupExtender char.val

/-- Check if character is a regional indicator character

  Unicode property: `Regional_Indicator` -/
@[inline]
public def isRegionalIndicator (char : Char) : Bool := lookupRegionalIndicator char.val

/-- Check if character is a diacritic character

  Unicode property: `Diacritic` -/
@[inline]
public def isDiacritic (char : Char) : Bool := lookupDiacritic char.val

/-- Check if character is a sentence terminal character

  Unicode property: `Sentence_Terminal` -/
@[inline]
public def isSentenceTerminal (char : Char) : Bool := lookupSentenceTerminal char.val

/-- Check if character is a pattern syntax character

  Unicode property: `Pattern_Syntax` -/
@[inline]
public def isPatternSyntax (char : Char) : Bool := lookupPatternSyntax char.val

/-- Check if character is a pattern white space character

  Unicode property: `Pattern_White_Space` -/
@[inline]
public def isPatternWhiteSpace (char : Char) : Bool := lookupPatternWhiteSpace char.val
