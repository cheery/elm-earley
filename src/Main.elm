module Main exposing (..)

import Browser
import Html exposing (..)
import Html.Attributes exposing (..)
import Html.Events exposing (onInput, onClick)
import Http

import Array exposing (..)
import Set exposing (..)
import Dict exposing (..)
import Maybe exposing (..)
import String exposing (fromInt)

type alias Rule = (String, List String)
type alias Grammar = Array Rule
type alias Terminals = Set String

type alias EIM = (Int, Int, Int)

origin : EIM -> Int
origin (o,_,_) = o

rule : EIM -> Grammar -> Rule
rule (_,index,_) grammar = case Array.get index grammar of
    Just a -> a
    Nothing -> unreachable_at_rule

type Dot = Shift String
         | Reduce String

dot : EIM -> Grammar -> Dot
dot eim grammar =
    let (_,index,pos) = eim
        (lhs,rhs) = rule eim grammar
    in case List.drop pos rhs of
        (x :: _) -> Shift x
        []       -> Reduce lhs

justindex lst i unreachable = justhead (List.drop i lst) unreachable

justhead lst unreachable = case lst of
    [] -> unreachable
    (x :: _) -> x

eim_increment offset (o,i,pos) = (o+offset,i,pos+1)

eime_increment : Int -> Int -> EIME -> EIME
eime_increment offset err ((o,i,pos),e) = ((o+offset,i,pos+1),e+err)


-- Edit-distance-augmented EIM.
type alias EIME = (EIM, Int)

-- Preparation for parsing
-- Construct leftmost transitive closure & skipcosts
construct_parser : Grammar -> Terminals -> Parsing
construct_parser grammar terminals =
    let skipcost = compute_skipcost grammar terminals
    in { grammar = grammar
       , skipcost = skipcost
       , leftmost_tr = transitive (leftmost (Array.toList grammar) skipcost)
       }

type alias Parsing =
    { grammar : Grammar
    , leftmost_tr : Dict String (Set String)
    , skipcost : Dict String Int
    }

leftmost : List Rule -> Dict String Int -> Dict String (Set String)
leftmost rules skipcost = case rules of
    [] -> Dict.empty
    ((lhs,rhs) :: rest) -> List.foldl
        (mselect lhs)
        (leftmost rest skipcost)
        (leftmost_rhs rhs skipcost)

leftmost_rhs rhs skipcost = case rhs of
    [] -> []
    (x :: rest) -> if (Dict.get x skipcost == Just 0)
        then (x :: leftmost_rhs rest skipcost)
        else [x]

terminal_skipcosts : Terminals -> Dict String Int
terminal_skipcosts terminals = Set.foldl
    (\sym -> Dict.insert sym 1) Dict.empty terminals

compute_skipcost : Grammar -> Terminals -> Dict String Int
compute_skipcost grammar terminals = 
    get_fixed_point
        (each (List.map rule_to_skipcost (Array.toList grammar)))
        (terminal_skipcosts terminals)

rule_to_skipcost : Rule -> Dict String Int -> Maybe (Dict String Int)
rule_to_skipcost (lhs, rhs) costs =
    case compute_skipcost_sum costs rhs of
        Nothing -> Nothing
        Just i -> case Dict.get lhs costs of
            Just k -> if i < k
                then Just (Dict.insert lhs i costs)
                else Nothing
            Nothing -> Just (Dict.insert lhs i costs)

compute_skipcost_sum : Dict String Int -> List String -> Maybe Int
compute_skipcost_sum costs rhs = case rhs of
    [] -> Just 0
    (x :: r) -> Maybe.map2 (+)
        (Dict.get x costs)
        (compute_skipcost_sum costs r)


-- The EIME-augmented parsing routine.
build_eimes : Parsing -> String -> List String -> Set EIME
build_eimes pars accept input =
    toSet (step_eime pars [] (fromEIMEList (predict2 pars accept)) input)

step_eime : Parsing -> List (Dict EIM Int) -> Dict EIM Int -> List String -> Dict EIM Int
step_eime pars state last input = case input of
    [] -> last
    (sym :: rest) ->
        let scanseed = (scan2_seed pars sym last 1)
            deepscan prev vis (eim,e) s = case dot eim pars.grammar of
                (Reduce sym2) ->
                    let sns = scan2 pars sym2
                            (justindex prev (origin eim - 1) (Dict.empty))
                            (origin eim) e
                    in List.foldl vis s sns
                (Shift sym2) -> s
            ss = build_itemset (deepscan (last :: state)) scanseed Dict.empty
            -- Prediction includes empty item shifts,
            -- so it only needs to be done once.
            ss2 = predict_all2 pars ss
            -- Add items from the previous set to treat 'deletion'
            ss3 = addEIME (Dict.toList <| scoreup last) ss2
        in step_eime pars (last :: state) ss3 rest
            
scoreup : Dict EIM Int -> Dict EIM Int
scoreup ss = Dict.fromList (List.map (eime_increment 1 1) (Dict.toList ss))

-- Scan alone does "reduction" -only.
scan2 : Parsing -> String -> Dict EIM Int -> Int -> Int -> List EIME
scan2 pars sym state offset err =
    List.map (eime_increment offset err)
    << Dict.toList
    <| Dict.filter
       (\eim e -> dot eim pars.grammar == Shift sym) state

-- The seed scan does "scan/replace" -semantics.
scan2_seed : Parsing -> String -> Dict EIM Int -> Int -> List EIME
scan2_seed pars sym state offset =
    let select (eim,e) = case dot eim pars.grammar of
            Shift s -> if s == sym
                then Just (eime_increment offset 0 (eim,e))
                else Just (eime_increment offset 1 (eim,e))
            Reduce _ -> Nothing
    in List.filterMap select (Dict.toList state)

eim_to_eime : EIM -> EIME
eim_to_eime eim = (eim,0)


-- The EIME-augmented prediction routines.
predict_all2 : Parsing -> Dict EIM Int -> Dict EIM Int
predict_all2 pars ss =
    let
        predict_dot : EIME -> List EIME
        predict_dot (eim,e) = case dot eim pars.grammar of
            Shift sym -> predict2 pars sym
            Reduce sym -> []
    in List.foldl (addEIME << predict_dot) ss (Dict.toList ss)

predict2 : Parsing -> String -> List EIME
predict2 pars sym = (List.concat (List.map (predict_smear2 pars)
    (List.filterMap (choose_by_lhs2 (Set.insert sym (mget sym pars.leftmost_tr)))
        (List.indexedMap Tuple.pair (Array.toList pars.grammar)))))

choose_by_lhs2 : Set String -> (Int, Rule) -> Maybe EIME
choose_by_lhs2 syms (ndex, (lhs, rhs)) = if (Set.member lhs syms)
    then Just ((0, ndex, 0), 0)
    else Nothing

predict_smear2 : Parsing -> EIME -> List EIME
predict_smear2 pars (eim,e) = case get_skipcost pars eim of
    Nothing -> [(eim,e)]
    Just k -> ((eim,e) :: predict_smear2 pars (eim_increment 0 eim, e+k))

get_skipcost : Parsing -> EIM -> Maybe Int
get_skipcost pars eim = case dot eim pars.grammar of
    Reduce _ -> Nothing
    Shift sym -> Dict.get sym pars.skipcost


-- Derive new items until there are no more items to derive.
type alias EIS = (List EIME, Dict EIM Int)

build_itemset : ((EIME -> EIS -> EIS) -> EIME -> EIS -> EIS) -> List EIME
    -> Dict EIM Int -> Dict EIM Int
build_itemset visit eimes ini =
    let insert : EIME -> EIS -> EIS
        insert (eim,e) (q, ss) = case Dict.get eim ss of
            Nothing -> ((eim,e) :: q, Dict.insert eim e ss)
            Just k -> if k <= e
                then (q, ss)
                else ((eim,e) :: q, Dict.insert eim e ss)
        loop : EIS -> Dict EIM Int
        loop (q, ss) = case q of
            [] -> ss
            (eime :: q2) -> loop (visit insert eime (q2,ss))
    in loop (List.foldl insert ([], ini) eimes)


type alias Model =
    { grammar : Grammar
    , terminals : List String
    , input : List String
    , accept : String
    }

type Msg = AddTerminal String
         | Reset
         | Back

main : Program () Model Msg
main = Browser.element
    { init = init
    , update = update
    , subscriptions = subscriptions
    , view = view
    }

init _ =
    ( { grammar = Array.fromList
            [ ("program", ["expr"])
            , ("expr", ["mul"])
            , ("mul", ["add"])
            , ("mul", ["mul", "*", "add"])
            , ("add", ["call"])
            , ("add", ["add", "+", "call"])
            , ("call", ["term"])
            , ("call", ["call", "term"])
            ]
      , terminals = ["term", "*", "+"]
      , input = []
      , accept = "program"
      }, Cmd.none)

update : Msg -> Model -> (Model, Cmd Msg)
update msg model =
    ( case msg of
        AddTerminal t -> { model | input = model.input ++ [t] }
        Reset -> { model | input = [] }
        Back -> { model | input = List.take (List.length model.input - 1) model.input }
    , Cmd.none)

subscriptions model = Sub.none

view model = div []
    [ p [ style "margin" "1em"]
        [text "Calculates language edit distance using Earley's algorithm"]
    , div [ style "border" "1px gray solid"
          , style "margin" "1em 1em"
          , style "padding" "1ex" ]
        ([ div
            [ style "margin-top" "-2.4ex"
            , style "background-color" "white"
            , style "width" "5em"
            , style "border" "1px gray solid"
            , style "padding-left" "1ex"
            , style "margin-bottom" "0.2em"
            ] [ text "Grammar" ] ] ++
         (List.map view_rule (Array.toList model.grammar)))
    , div
        [ style "margin" "1em 1em"
        ] ([ button [onClick (Reset), style "margin-right" "0ex"] [text "reset"]
           , button [onClick (Back), style "margin-right" "2ex"] [text "←"]
           ]
          ++ List.map (\t -> button [
            onClick (AddTerminal t) ] [text t]) model.terminals
          )
    , div
        [ style "margin" "1em 1em" ]
        ([text "input: "] ++ (case model.input of
            [] -> [text "[empty]"]
            _  -> List.intersperse (text " ") (List.map text model.input)))
    , div
        [ style "margin" "1em 1em", style "border-top" "1px dashed gray" ]
        [ let pars = construct_parser model.grammar (Set.fromList model.terminals)
          in view_eims pars
            (build_eimes pars model.accept model.input) ]
    , div
        [ style "margin" "1em 1em", style "border-top" "1px dashed gray" ]
        [
          p [] [text "The display shows the last itemset built."]
        , p [] [text "The blue circle is the 'dot'"]
        , p [] [text "The green slashed number tells the edit distance."]
        , p [] [text "The braces tell how many symbols match on the item."]
        ]
    ]

view_rule (lhs, rhs) =
    div [ ]
        [ text (lhs ++ " → ")
        , span [] (List.intersperse (text " ") (List.map text rhs))
        ]

view_eims : Parsing -> Set EIME -> Html Msg
view_eims pars eime = div [style "margin" "1em 1em"]
    (List.map
        (view_eime pars)
        (List.sortBy eime_sortcond (Set.toList eime)))

eime_sortcond : EIME -> ((Int, Int, Int), Int)
eime_sortcond ((o,i,p), e) = ((-o,e,i),p)

view_eime : Parsing -> EIME -> Html Msg
view_eime pars (eim,err) =
    let
        (o,i,pos) = eim
        (lhs, rhs) = rule eim pars.grammar
        before = List.take pos rhs
        after = List.drop pos rhs
    in div [] (
        [text lhs, span [style "color" "blue"] [text " → "]]
        ++ List.intersperse (text " ") (List.map text before)
        ++ [span [style "color" "blue"] [text " ∘ "]]
        ++ List.intersperse (text " ") (List.map text after)
        ++ (if origin eim == 0 then [] else [text " ",
            span [style "color" "#ccc"]
                [text "{", text (fromInt (origin eim)), text "}"]])
        ++ (if err == 0 then [] else [text " ",
            span [ style "color" "green"
                 , style "font-size" "75%" ] [text (" / " ++ fromInt err)]])
        )



-- Represents set of relations betveen values.
type alias DictSet k v = Dict k (Set v)

mget : comparable -> DictSet comparable v -> Set v
mget key ds = case Dict.get key ds of
    Just a  -> a
    Nothing -> Set.empty

mselect : comparable1 -> comparable2
    -> DictSet comparable1 comparable2
    -> DictSet comparable1 comparable2
mselect key value ds = Dict.update key (minsert value) ds

minsert : comparable -> Maybe (Set comparable) -> Maybe (Set comparable)
minsert item mb = case mb of
    Nothing -> Just (Set.singleton item)
    Just a  -> Just (Set.insert item a)


-- Compute transitive closure of a relation
transitive : DictSet comparable comparable -> DictSet comparable comparable
transitive = get_fixed_point find_transition

find_transition : DictSet comparable comparable
    -> Maybe (DictSet comparable comparable)
find_transition ds = each (List.map bmid (Dict.toList ds)) ds

bmid : (comparable, Set comparable)
    -> DictSet comparable comparable -> Maybe (DictSet comparable comparable)
bmid (lhs, middle) = each (List.map (fmid lhs middle) (Set.toList middle))

fmid : comparable -> Set comparable -> comparable
    -> DictSet comparable comparable -> Maybe (DictSet comparable comparable)
fmid lhs middle rhs ds =
    let tr = Set.union (mget rhs ds) middle
    in if (Set.size middle) < (Set.size tr)
        then Just (Dict.insert lhs (Set.union middle tr) ds)
        else Nothing


-- Repeats the task until the refinement function no longer refines.
get_fixed_point : (a -> Maybe a) -> a -> a
get_fixed_point fn a = case fn a of
    Nothing -> a
    Just b -> get_fixed_point fn b

-- Tools to build up the fixed point function above.
either : (a -> Maybe a) -> (a -> Maybe a) -> a -> Maybe a
either f g a = case f a of
    Nothing -> g a
    Just b -> Just (Maybe.withDefault b (g b))

each : List (a -> Maybe a) -> a -> Maybe a
each seq a = List.foldl either (\m -> Nothing) seq a


-- Small util to switch between dicts and sets
fromEIMESet : Set EIME -> Dict EIM Int
fromEIMESet s = fromEIMEList (Set.toList s)

toSet : Dict comparable1 comparable2 -> Set (comparable1,comparable2)
toSet d = Set.fromList (Dict.toList d)

addEIME : List EIME -> Dict EIM Int -> Dict EIM Int
addEIME eime s =
    let
        lowest e weight = case weight of
            Just k  -> Just (Basics.min k e)
            Nothing -> Just e
        insertEIME (eim,e) ss = Dict.update eim (lowest e) ss
    in List.foldl insertEIME s eime

fromEIMEList : List EIME -> Dict EIM Int
fromEIMEList eimes = addEIME eimes Dict.empty


fixpoint : (a -> a) -> a
fixpoint f = f (fixpoint f)

-- Just causes stack to overflow, needs something better here.
-- unreachable : a
-- unreachable = fixpoint (\x -> x)

unreachable_at_rule : Rule
unreachable_at_rule = ("", [])
