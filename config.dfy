abstract module orca{
////////////////////CONFIG////////////////////
datatype Config = createConfig(heap: Heap, actors: Actors)

//Heap 
datatype Heap = CHeap(objs: map<Addr, map<FId, Addr>>)

//Addrs
datatype Addr = OA(oa: ObjectAddr) | AA(aa: ActorAddr) | ERR
type ObjectAddr = nat
type ActorAddr = nat
/* 
datatype Addr = Cons(id: int)
datatype ObjectAddr = Cons(id: int)
datatype ActorAddr = Cons(id: int) 
*/

//type Actors = map<ActorAddr, Actor>
type Actors = seq<Actor>
//datatype Queue = CQueue(msgs: seq<Msg>)
type Queue = seq<Msg>
//datatype Msg = orca(i: Addr, z: int) | app(b: BId, is: seq<ObjectAddr>)
datatype Msg = orca(i: Addr, z: int) | app(f: Frame) // ..alternative: only a frame is passed
//type Actor = (q: Queue, rct: RefCountT, s: State)
datatype Actor = CActor(q: Queue, rct: RefCountT, st: State, cl: ClassId)
type RefCountT = map<Addr, int>

//Paths 
datatype DP = This | LP(zero: int, x: VarId) | MP(k: int, x': VarId) | cons(dp: DP, f: FId)
datatype SP = This | bsp(b: BId, x: VarId) | cons(sp: SP, f: FId)
datatype Capability = WRITE | READ | TAG | ERR

//State 
datatype State = idl | exe(f: Frame) | snd(f': Frame, a: Actor, m: Msg, ws: Workset)
                | mkU(ms: Marks) | trc(ms': Marks) | mkR(ms'': Marks) | cll(ms''': Marks)
datatype Frame = CFrame(b: BId, Map: map<VarId, Addr>)
type Workset = set<Addr> 
//datatype Marks = CMarks(map<Addr, RU>)
type Marks = map<Addr, RU>

datatype RU = R | U

//IDs
type FId = int 
type BId = int
type ClassId = int
type VarId = int

//type Class = map<ActorAddr, ClassId>
//now that Class is not a map, sees needs the config 
/*
predicate sees(a: ActorAddr, sp: SP, c: Config, cappa: Capability)
{
    if 0 <= a < |c.actors| then sees'(c.actors[a].cl, sp, cappa) else false 
}
*/

//predicate sees(cid: ClassId, sp: SP, cappa: Capability)

function sees(cid: ClassId, sp: SP) : Capability

lemma {:verify true} A1(a: Actor, sp: SP, f: FId, cappa: Capability) 
requires sees(a.cl, SP.cons(sp, f)) == cappa //pass cappa as param instead?
ensures exists cappa' :: cappa' != TAG && sees(a.cl, sp) == cappa' 


lemma {:verify true} A2(a: Actor, sp: SP, f: FId) 
requires sees(a.cl, SP.cons(sp, f)) == WRITE
ensures sees(a.cl, sp) == WRITE

/*
lemma {:verify true} A1(a: Actor, sp: SP, f: FId, cappa: Capability) 
requires sees(a.cl, SP.cons(sp, f), cappa) //pass cappa as param instead?
ensures exists cappa' :: cappa' != TAG && sees(a.cl, sp, cappa')  
{
    assume true;
    //assume exists cappa' :: cappa' != TAG && sees(a.cl, sp, cappa');
    //assert exists cappa' :: cappa' != TAG && sees(a.cl, sp, cappa');
}

lemma {:verify true} A2(c: Config, a: Actor, sp: SP, f: FId) 
requires sees(a.cl, SP.cons(sp, f), WRITE)
ensures sees(a.cl, sp, WRITE)
{
    assume sees(a.cl, sp, WRITE);
}
*/
/*
DO NOT VERIFY
lemma {:verify false} A1(a: Actor, sp: SP, f: FId, cappa: Capability) 
requires sees(a.cl, SP.cons(sp, f), cappa) //pass cappa as param instead?
ensures exists cappa' :: cappa' != TAG && sees(a.cl, sp, cappa')  
{
}

lemma {:verify false} A2(c: Config, a: Actor, sp: SP, f: FId) 
requires sees(a.cl, SP.cons(sp, f), WRITE)
ensures sees(a.cl, sp, WRITE)
{
}
*/

/*
OLD VERSION
lemma {:verify false} A1(c: Config, a: ActorAddr, sp: SP, f: FId, cappa: Capability) 
requires sees(a, SP.cons(sp, f), c) == cappa //pass cappa as param instead?
ensures exists cappa' :: cappa' != TAG && sees(a, sp, c) == cappa' 
{
}

lemma {:verify false} A2(c: Config, a: ActorAddr, sp: SP, f: FId) 
requires sees(a, SP.cons(sp, f), c) == WRITE
ensures sees(a, sp, c) == WRITE
{
}
*/

/*
//TODO: USELESS REMOVE
predicate MP_wf(a: Actor, k: int) 
{
    0 <= k < |a.q| 
}

//TODO: USELESS REMOVE
//can we assume this?
lemma {:verify false} all_actors_in_config()
ensures forall a: ActorAddr, c: Config :: 0 <= a < |c.actors|
{
}
*/

//C FINAL 
//TODO: WRITE FUNCTIONS FOR THINGS LIKE msg.f.Map[x] -> F(msg, x)
function method C(a: ActorAddr, dp: DP, c: Config) : Addr 
{
    //TODO: REMOVE ASSUMPTION
    assume 0 <= a < |c.actors|;
    match dp 
    case This => AA(a)
    case MP(k, x) => 
        (
        //TODO: REMOVE ASSUMPTION
        assume 0 <= k < |c.actors[a].q|;
        var msg := c.actors[a].q[k];
        if msg.app? then 
            (if x in msg.f.Map then msg.f.Map[x] else Addr.ERR) 
        else Addr.ERR)
    case LP(zero, x) =>
        (var state := c.actors[a].st;
        if state.exe? then 
            (if x in state.f.Map then state.f.Map[dp.x] else Addr.ERR)
        else Addr.ERR)
    case cons(p, f) => 
        assume C(a, p, c) in c.heap.objs;
        var obj := c.heap.objs[C(a, p, c)];
        if f in obj then obj[f] else Addr.ERR
}
//TODO: USE PREDICATE OR REMOVE 
function valid_addr(l: Addr) : bool {
    true
}
}
