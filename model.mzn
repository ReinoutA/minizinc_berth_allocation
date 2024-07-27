%%% Reinout Annaert 4ELICT

int: N; % Aantal Vessels
int: L; % Lengte van Quay
int: d; % Minimum Safety Distance
int: C; % Aantal Kranen
int: r; % Range Kraan
int: s; % Maximum Timeshift

set of int: positie = 0..L;
set of int: kraan = 1..C;
set of int: time = 0..(24*7);
set of int: vessel = 1..N;
array[1..N] of var int: departuretimes;
array[1..N] of var 0..C: minimumnumqcs;
array[int] of var 0..L: qcbasepositions;
array[1..N] of var 1..L: lengths;
array[1..N] of var int: arrivaltimes;

% Vars
array[vessel] of var positie: vesselPosities;
array[vessel] of var time: startTimes;
array[vessel] of var time: departureTimes;
array[time, 1..C] of var 0..N: schedule;
array[vessel, vessel] of var bool: positieOverlap;
array[vessel, vessel] of var bool: timeOverlap; 
array[vessel, kraan] of var bool: toewijzing;

% Ensure that the position of a vessel is valid and does not exceed the quay length
constraint forall(v in vessel) (L >= lengths[v] + vesselPosities[v]);

% Ensure vessel has the minimum amount QCS
constraint forall(v in vessel, k in kraan) (
    if schedule[startTimes[v], k] = v then
        toewijzing[v, k] = 1
    else
        toewijzing[v, k] = 0
    endif
);

% Ensure vessel is in the range of QC
constraint forall(v in vessel, k in kraan) (
    if schedule[startTimes[v], k] = v then
        r + qcbasepositions[k] >= vesselPosities[v] + lengths[v] /\ qcbasepositions[k] <= vesselPosities[v]
    endif
);

% Ensure that positions cant overlap at a certain timestamp
constraint forall(v_1 in vessel, v_2 in vessel) (
    not(positieOverlap[v_1, v_2] /\ v_1 != v_2 /\ timeOverlap[v_1, v_2])
);

% Ensure that the departure time is correctly calculated within the cyclic schedule
constraint forall(v in vessel) (departureTimes[v] = (departuretimes[v] + startTimes[v] - arrivaltimes[v]) mod (24*7));

% Ensure that you dont go over timeshift of s 
constraint forall(v in vessel) (startTimes[v] <= (s + arrivaltimes[v]) mod (24*7) /\ startTimes[v] >= arrivaltimes[v]);

% Ensure that positions don't overlap spatially
constraint forall(v_1 in vessel, v_2 in vessel) (
    if (vesselPosities[v_1] <= d + vesselPosities[v_2] + lengths[v_2] /\ d + vesselPosities[v_1] + lengths[v_1] >= vesselPosities[v_2]) then
        positieOverlap[v_1, v_2] = 1
    endif
);

% Ensure that there is no time overlap between vessels
constraint forall(v_1 in vessel, v_2 in vessel) (
    if (
        (departureTimes[v_2] <= startTimes[v_2] /\ departureTimes[v_1] >= startTimes[v_2]) 
        \/
        (startTimes[v_1] <= departureTimes[v_2] /\ departureTimes[v_1] >= startTimes[v_2]) 
        \/
        (departureTimes[v_1] <= startTimes[v_1] /\ departureTimes[v_2] >= startTimes[v_1])
    ) then
        timeOverlap[v_1, v_2] = 1
    endif
);

% Ensure that vessels are served by the same QC over their entire time period
constraint forall(v in vessel) (
    sum(k in kraan)(schedule[startTimes[v], k] = v) >= minimumnumqcs[v] 
    /\
    sum(k in kraan)(schedule[departureTimes[v], k] = v) >= minimumnumqcs[v]
);

% Ensure that vessels are served by the same QC over their entire time period (continued)
constraint forall(v in vessel, k in kraan) (
    if startTimes[v] < departureTimes[v] then
        (sum(t in startTimes[v]..departureTimes[v])(schedule[t, k] = v) = departureTimes[v] - startTimes[v] + 1) 
        \/
        (sum(t in startTimes[v]..departureTimes[v])(schedule[t, k] = v) = 0)
    endif
);

% Ensure that vessels are served by the same QC over their entire time period (continued)
constraint forall(v in vessel, k in kraan) (
    if startTimes[v] > departureTimes[v] then
        (sum(t in 0..departureTimes[v])(schedule[t, k] = v) = departureTimes[v] + 1) 
         \/
        (sum(t in 0..departureTimes[v])(schedule[t, k] = v) = 0)
    endif
);

% Ensure that vessels are served by the same QC over their entire time period (continued)
constraint forall(v in vessel, k in kraan) (
    if startTimes[v] > departureTimes[v] then
        (sum(t in startTimes[v]..(24*7))(schedule[t, k] = v) = (24*7) - startTimes[v] + 1) 
        \/
        (sum(t in startTimes[v]..(24*7))(schedule[t, k] = v) = 0)
    endif
);

% Ensure that a vessel is not served outside the possible hours
constraint forall(v in vessel, k in kraan) (
    if startTimes[v] < departureTimes[v] then
        sum(t in 0..(startTimes[v] - 1))(schedule[t, k] = v) = 0
    endif
);

% Ensure that a vessel is not served outside the possible hours (continued)
constraint forall(v in vessel, k in kraan) (
    if startTimes[v] < departureTimes[v] then
        sum(t in (departureTimes[v] + 1)..(24*7))(schedule[t, k] = v) = 0
    endif
);

% Ensure that a vessel is not served outside the possible hours (continued)
constraint forall(v in vessel, k in kraan) (
    if startTimes[v] > departureTimes[v] then
        sum(t in (departureTimes[v] + 1)..startTimes[v] - 1)(schedule[t, k] = v) = 0
    endif
);
% find feasible solution
solve satisfy;

output [
    "\(v):\(vesselPosities[v])-\(lengths[v]+vesselPosities[v]);\(startTimes[v])..\(departureTimes[v]);" ++  (join(",", [show(kr) | kr in kraan where fix(toewijzing[v, kr] = 1)])) ++ "\n" | v in vessel
];
