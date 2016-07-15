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
/*
//pass maps around?
function sees(cl: Class, a: ActorAddr, sp: SP) : Capability
{
    if a in cl then sees'(cl[a], sp) else Capability.ERR
}

function sees'(cid: ClassId, sp: SP) : Capability

lemma A1(c: Config, cl: Class, a: ActorAddr, sp: SP, f: FId, cappa: Capability) 
requires sees(cl, a, SP.cons(sp, f)) == cappa //pass cappa as param instead?
//requires sees(cl, c, a, SP.cons(sp, f)) == _ 
ensures exists cappa' :: cappa' != TAG && sees(cl, a, sp) == cappa'

lemma A2(c: Config, cl: Class, a: ActorAddr, sp: SP, f: FId) 
requires sees(cl, a, SP.cons(sp, f)) == WRITE
ensures sees(cl, a, sp) == WRITE


/*
function method C(a: ActorAddr, dp: DP, c: Config) : Addr 
{
    all_actors_in_config();
    match dp 
    case This => AA(a)
    //case LP(zero, x) => if c.actors[a].st == exe(f: Frame) then {Capability.ERR} else {ERR}
    case MP(k, x) => 
        match c.actors[a].q[k] 
        case app(f) => f.Map[x]
        case orca(_, _) => Addr.ERR
    case LP(zero, x) => 
        match c.actors[a].st 
        //add wf of frames?
        case exe(f) => if x in f.Map then f.Map[x] else Addr.ERR
        case snd(_, _, _, _) => Addr.ERR
        case idl => Addr.ERR
        case mkU(_) => Addr.ERR
        case trc(_) => Addr.ERR
        case mkR(_) => Addr.ERR
        case cll(_) => Addr.ERR
}


lemma MP_wf(a: Actor, k: int) 
ensures 0 <= k < |a.q| 

//can we assume this?
lemma all_actors_in_config()
ensures forall a: ActorAddr, c: Config :: a in c.actors

function method valid_addr(l: Addr) : bool {
    true
}

function method C(a: ActorAddr, dp: DP, c: Config) : Addr 
{
    all_actors_in_config();
    match dp 
    case This => AA(a)
    case MP(k, x) =>
        MP_wf(c.actors[a], k);
        CMP(k, x, c, c.actors[a]) 
    case LP(zero, x) =>
        CLP(zero, x, c, c.actors[a]) 
    case cons(p, f) => 
        assume C(a, p, c) in c.heap.objs;
        var obj := c.heap.objs[C(a, p, c)];
        if f in obj then obj[f] else Addr.ERR
}
function method CLP(zero: int, x: VarId, c: Config, a: Actor) : Addr
{   
    match a.st 
    //add wf of frames?
    case exe(f) => if x in f.Map then f.Map[x] else Addr.ERR
    case snd(_, _, _, _) => Addr.ERR
    case idl => Addr.ERR
    case mkU(_) => Addr.ERR
    case trc(_) => Addr.ERR
    case mkR(_) => Addr.ERR
    case cll(_) => Addr.ERR
}

function method CMP(k: int, x: VarId, c: Config, a: Actor) : Addr
requires 0 <= k < |a.q|
{
    assert 0 <= k < |a.q|;
    match a.q[k] 
    case app(f) => if x in f.Map then f.Map[x] else Addr.ERR
    case orca(_, _) => Addr.ERR
}
*/
