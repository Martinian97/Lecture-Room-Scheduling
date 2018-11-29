from z3 import *
from datetime import datetime,timedelta
import json,csv

with open("input.json") as readfile :
	a = readfile.read()

a = a.strip()
obj = json.loads(a)
room = obj['Room Types']
timeSlots = obj['Institute time']
Classrooms = obj['Classrooms']
courses,profs,batches,course_roomType,course_duration,coursecodes,codecourse_roomtype,rooms,room_time,prof_time,batch_time = set(),set(),set(),set(),set(),set(),set(),set(),set(),set(),set()
s = Solver()
p,temp,starttimes,days=[],[],[],["Monday","Tuesday","Wednesday","Thursday","Friday"]
A,B,C,D,E,F,G={},{},{},{},{},{},{}
Time = {
	'1':[],
	'1.5':[],
	'2':[],
	'3':[]
}

for i in obj['Courses']:
	coursecodes.add(i[0])
	for k in range(len(i[2])):
		r=i[0]+'-'+str(k)
		courses.add(r) 
		course_duration.add((r,i[2][0]))
		codecourse_roomtype.add((r,i[1]))
	for j in i[3]:
		j = j.split()[0]
		profs.add(j)
	batches.add(i[4])
	course_roomType.add((i[0],i[1]))

# A proposition.. prof, course
prof_course = set()
Professors = {}
for i in obj["Courses"]:
	for prof in i[3]:
		prof1 = prof.split()[0]
		Professors[prof1] = str(prof)
		if(A.get(prof1)==None):
			A[prof1]={}
		prof_course.add((prof1,i[0]))

realprofcourse = set()
for k in prof_course:
	for course in courses:
		code=course.split('-')[0]
		if(code==k[1]):
			A[k[0]][course]=Bool('A_'+k[0]+'_'+course)
			if(course not in temp):
				s.add(A[k[0]][course])
				realprofcourse.add((Professors[k[0]],str(code)))
				temp.append(course)

for k in Classrooms:
	B[k[0]]={}
	rooms.add(k[0])

# B proposition.. room, course
for j in Classrooms:
	for i in codecourse_roomtype:
		if(i[1]==j[1]):
			B[j[0]][i[0]]=Bool('B_'+j[0]+'_'+i[0])

# E proposition.. batch, course
batch_course = set()
for i in obj["Courses"]:
	E[i[4]]={}
	batch_course.add((i[4],i[0]))

for t in batch_course:
	for k in courses:
		code = k.split('-')[0]
		if(code==t[1]):
			E[t[0]][k]=Bool('E_'+str(t[0])+'_'+k)
			s.add(E[t[0]][k])

for slot in timeSlots:
	starttimes = [] 
	start=datetime.strptime(slot[0],"%H:%M")
	end=datetime.strptime(slot[1],"%H:%M")
	endy=end-timedelta(hours=1)
	while(True):
		starttimes.append(start)
		if(start.time()==endy.time()):
			break
		start = (start+timedelta(minutes=30))
	for hour in Time:
		for time in starttimes:
			h = float(hour)
			x = time+timedelta(hours=h)
			duration = str(time.time())[:5]+'-'+str(x.time())[:5]
			if(x>end):
				continue
			Time[hour].append(duration)	
 
# D proposition.. course and time
temp,temp2 = [],[]
for c in course_duration:
	D[c[0]]={}
	for day in days:
		D[c[0]][day]={}
		for j in Time:
			if(c[1]==float(j)):
				for k in Time[j]:
					D[c[0]][day][k]=Bool('D_'+c[0]+'_'+day+'_'+k)
					code = c[0].split('-')[0]

# C proposition.. room and time
for i in obj["Courses"]:
	room_time.add((i[1],i[2][0]))

for t in room_time:
	duration = t[1]
	roomtype = t[0]
	for i in Classrooms:
		if(i[1]==roomtype):
			if(C.get(i[0])==None):
				C[i[0]]={}
			for day in days:
				if(C[i[0]].get(day)==None):
					C[i[0]][day]={}
				for j in Time:
					if(float(j)==duration):
						for k in Time[j]:
							C[i[0]][day][k]=Bool('C_'+i[0]+'_'+day+'_'+k)

#Constraint for overlapping time
for i in Classrooms:
	if(C.get(i[0])==None):
		continue
	for day in days:
		for j in Time:
			for k in Time[j]:
				if(C[i[0]][day].get(k)==None):
					continue
				initial=C[i[0]][day][k]
				start=datetime.strptime(k.split('-')[0],"%H:%M")
				end=datetime.strptime(k.split('-')[1],"%H:%M")
				for j2 in Time:
					for k2 in Time[j2]:
						if(C[i[0]][day].get(k2)==None):
							continue
						start2=datetime.strptime(k2.split('-')[0],"%H:%M")
						end2=datetime.strptime(k2.split('-')[1],"%H:%M")
						if(start==start2 and end==end2):
							continue
						elif(start2<=start and end2>start):
							s.add(Implies(initial,Not(C[i[0]][day][k2])))
						elif(start2>=start and start2<end):
							s.add(Implies(initial,Not(C[i[0]][day][k2])))

# F proposition.. prof and time
for i in obj["Courses"]:
	for prof in i[3]:
		prof = prof.split()[0]
		if(F.get(prof)==None):
			F[prof]={}
		prof_time.add((prof,i[2][0]))

for t in prof_time:
	duration = t[1]
	c = t[0]
	for day in days:
		if(F[c].get(day)==None):
			F[c][day]={}
		for j in Time:
			if(float(j)==duration):
				for k in Time[j]:
					F[c][day][k]=Bool('F_'+c+'_'+day+'_'+k)

#Constraint for overlapping time
for i in profs:
	for day in days:
		for j in Time:
			for k in Time[j]:
				if(F[i][day].get(k)==None):
					continue
				initial=F[i][day][k]
				start=datetime.strptime(k.split('-')[0],"%H:%M")
				end=datetime.strptime(k.split('-')[1],"%H:%M")
				for j2 in Time:
					for k2 in Time[j2]:
						if(F[i][day].get(k2)==None):
							continue
						start2=datetime.strptime(k2.split('-')[0],"%H:%M")
						end2=datetime.strptime(k2.split('-')[1],"%H:%M")
						if(start==start2 and end==end2):
							continue
						elif(start2<=start and end2>start):
							s.add(Implies(initial,Not(F[i][day][k2])))
						elif(start2>=start and start2<end):
							s.add(Implies(initial,Not(F[i][day][k2])))
				
# G proposition.. batch and time
for i in obj["Courses"]:
	G[i[4]]={}
	batch_time.add((i[4],i[2][0]))

for t in batch_time:
	duration = t[1]
	c = t[0]
	for day in days:
		if(G[c].get(day)==None):
			G[c][day]={}
		for j in Time:
			if(float(j)==duration):
				for k in Time[j]:
					G[c][day][k]=Bool('G_'+str(c)+'_'+day+'_'+k)

#Constraint for overlapping time
for i in batches:
	for day in days:
		for j in Time:
			for k in Time[j]:
				if(G[i][day].get(k)==None):
					continue
				initial=G[i][day][k]
				start=datetime.strptime(k.split('-')[0],"%H:%M")
				end=datetime.strptime(k.split('-')[1],"%H:%M")
				
				for j2 in Time:
					for k2 in Time[j2]:
						if(G[i][day].get(k2)==None):
							continue
						start2=datetime.strptime(k2.split('-')[0],"%H:%M")
						end2=datetime.strptime(k2.split('-')[1],"%H:%M")
						if(start==start2 and end==end2):
							continue
						elif(start2<=start and end2>start):
							s.add(Implies(initial,Not(G[i][day][k2])))
						elif(start2>=start and start2<end):
							s.add(Implies(initial,Not(G[i][day][k2])))

# Constraint 1.. same time, 1 prof, 2 courses not possible
for day in days:
	for j in Time:
		for k in Time[j]:
			for prof in profs:
				for course1 in courses:
					if(D[course1][day].get(k)==None or A[prof].get(course1)==None):
						continue
					initial = And(A[prof][course1],D[course1][day][k])
					for course2 in courses:
						if(D[course2][day].get(k)==None or A[prof].get(course2)==None or (course1==course2)):
							continue
						s.add(Implies(initial,Not(And(A[prof][course2],D[course2][day][k]))))
					s.add(Implies(initial,F[prof][day][k]))

# Constraint 2.. same time, one batch, 2 courses not possible
for day in days:
	for j in Time:
		for k in Time[j]:
			for batch in batches:
				for course1 in courses:
					if(D[course1][day].get(k)==None or E[batch].get(course1)==None):
						continue
					initial = And(E[batch][course1],D[course1][day][k])
					for course2 in courses:
						if(D[course2][day].get(k)==None or E[batch].get(course2)==None or (course1==course2)):
							continue
						s.add(Implies(initial,Not(And(E[batch][course2],D[course2][day][k]))))
					s.add(Implies(initial,G[batch][day][k]))

# Constraint 3.. same time, one room, 2 courses not possible
for day in days:
	for j in Time:
		for k in Time[j]:
			for room in rooms:
				for course1 in courses:
					if(D[course1][day].get(k)==None or B[room].get(course1)==None):
						continue
					initial = And(B[room][course1],D[course1][day][k])
					for course2 in courses:
						if(D[course2][day].get(k)==None or (course1==course2) or B[room].get(course2)==None):	
							continue
						s.add(Implies(initial,Not(And(B[room][course2],D[course2][day][k]))))
					s.add(Implies(initial,C[room][day][k]))

#Constraint 4.. only one professor per course..
for course in courses:
	for prof1 in profs:
		if(A[prof1].get(course)==None):
			continue
		initial = A[prof1][course]
		for prof2 in profs:
			if(prof1==prof2 or A[prof2].get(course)==None):
				continue
			s.add(Implies(initial,Not(And(A[prof2][course]))))
	
# Constraint 5.. cs228-0 sharad => cs228-1 sharad and cs228-2 sharad and .....
c5=[]
for prof in profs:
	for course1 in courses:
		if(A[prof].get(course1)==None):
			continue
		initial = A[prof][course1]
		for course2 in courses:
			if(course1.split('-')[0]==course2.split('-')[0] and A[prof].get(course2)!=None):
				initial = And(A[prof][course2],initial)
		c5.append(Implies(A[prof][course1],initial))
	s.add(Or(c5))
	c5=[]

#constraint 6.. each course atleast one time
c6=[]
for course in course_duration:
	for day in days:
		for j in Time:
			for k in Time[j]:
				if(float(j)==course[1]):
					initial=D[course[0]][day][k]
					c6.append(initial)
	s.add(Or(c6))
	c6=[]

#constraint 6.5.. each course atleast one room
c6_5=[]
for course in codecourse_roomtype:
	for room in Classrooms:
		if(room[1]==course[1] and B[room[0]].get(course[0])!=None):
			initial=B[room[0]][course[0]]
			c6_5.append(initial)
	s.add(Or(c6_5))
	c6_5=[]

#constraint 7 .. each course exactly one time
for course in course_duration:
	for day in days:
		for j in Time:
			for k in Time[j]:
				if(D[course[0]][day].get(k)==None):
					continue
				elif(float(j)==course[1]):
					initial=D[course[0]][day][k]
					for day2 in days:
						for j2 in Time:
							for k2 in Time[j2]:
								if((D[course[0]][day2].get(k2)==None) or (day==day2 and k==k2)):
									continue
								s.add(Implies(initial,Not(D[course[0]][day2][k2])))

print str(s.check())

#check if sat or unsat
if(str(s.check())=='unsat'):
	exit()
m = (s.model())

# NOW getting timetable
true_A,true_B,true_C,true_D,true_E,true_F,true_G = list(),list(),list(),list(),list(),list(),list()
for t in m.decls():
		if is_true(m[t]):
			prop = str(t).split('_')
			if(prop[0]=='A'):
				true_A.append(str(t))
			elif(prop[0]=='B'):
				true_B.append(str(t))
			elif(prop[0]=='C'):
				true_C.append(str(t))
			elif(prop[0]=='D'):
				true_D.append(str(t))
			elif(prop[0]=='E'):
				true_E.append(str(t))
			elif(prop[0]=='F'):
				true_F.append(str(t))
			else:
				true_G.append(str(t))

prof_course = set()
for prop in true_A:
	i = prop.split('_')
	prof = i[1]
	course = i[2].split('-')[0]
	prof_course.add((prof,course))

batch_course = set()
for prop in true_E:
	i = prop.split('_')
	batch = i[1]
	course = i[2].split('-')[0]
	batch_course.add((batch,course))

course_room_time_prof_batch=set()
for prop in true_D:
	i = prop.split('_')
	course = i[1]
	day = i[2]
	time = i[3]
	for prop2 in true_B:
		j = prop2.split('_')
		room = j[1]
		course2 = j[2]
		if(course==course2):
			course = course.split('-')[0]
			for pc in prof_course:
				if(pc[1]==course):
					for bc in batch_course:
						if(bc[1]==course):
							for prop3 in true_C:
								k = prop3.split('_')
								room2 = k[1]
								day2 = k[2]
								time2 = k[3]
								if(room==room2 and day==day2 and time==time2):
									for prop4 in true_F:
										l = prop4.split('_')
										prof = l[1]
										day3 = l[2]
										time3 = l[3]
										if(prof==pc[0] and day==day3 and time==time3):
											for prop5 in true_G:
												m = prop5.split('_')
												batch = m[1]
												day4 = m[2]
												time4 = m[3]
												if(batch==bc[0] and day==day4 and time==time4):
													course_room_time_prof_batch.add((course,room,day,time,prof,batch))
	
# printing the timetable as CSV
timeslots = set()
Monday,Tuesday,Wednesday,Thursday,Friday = [],[],[],[],[]

for t in course_room_time_prof_batch:
    timeslots.add(t[3])
    if(t[2]=='Monday'):
        Monday.append(t)
    elif(t[2]=='Tuesday'):
        Tuesday.append(t)
    elif(t[2]=='Wednesday'):
        Wednesday.append(t)
    elif(t[2]=='Thursday'):
        Thursday.append(t)
    elif(t[2]=='Friday'):
        Friday.append(t)

timeslots = sorted(list(timeslots))
timeslots.insert(0,'Days')
timeslots.insert(1,'Rooms')

newMonday = [''] * len(timeslots) 
newMonday[0] = 'Monday'
newMonday[1] = 'T1'
newTuesday = [''] * len(timeslots)
newTuesday[0] = 'Tuesday'
newTuesday[1] = 'T1'
newWednesday = [''] * len(timeslots)
newWednesday[0] = 'Wednesday'
newWednesday[1] = 'T1'
newThursday = [''] * len(timeslots)
newThursday[0] = 'Thursday'
newThursday[1] = 'T1'
newFriday = [''] * len(timeslots)
newFriday[0] = 'Friday'
newFriday[1] = 'T1'

mt2 = [''] * len(timeslots)
mt2[0] = ''
mt2[1] = 'T2' 
mt3 = [''] * len(timeslots)
mt3[0] = ''
mt3[1] = 'T3' 
mlh1 = [''] * len(timeslots) 
mlh1[0] = ''
mlh1[1] = 'LH1'
mlh2 = [''] * len(timeslots) 
mlh2[0] = ''
mlh2[1] = 'LH2'
mlab = [''] * len(timeslots) 
mlab[0] = ''
mlab[1] = 'LAB'
mground = [''] * len(timeslots) 
mground[0] = ''
mground[1] = 'ground'

for entry in Monday:
    course = entry[0]
    room = entry[1]
    time = entry[3]
    prof = entry[4]
    batch = entry[5]
    i = timeslots.index(time)
    if(room=='T1'):
        newMonday[i] += ' ('+course+') '
    elif(room=='T2'):
        mt2[i] += ' ('+course+') '
    elif(room=='T3'):
        mt3[i] += ' ('+course+') '
    elif(room=='LH1'):
        mlh1[i] += ' ('+course+') '
    elif(room=='LH2'):
        mlh2[i] += ' ('+course+') '
    elif('LAB' in room or 'lab' in room or 'Lab' in room):
        mlab[i] += ' ('+course+','+room+') '
    elif(room=='ground'):
        mground[i] += ' ('+course+') '

tt2 = [''] * len(timeslots)
tt2[0] = ''
tt2[1] = 'T2' 
tt3 = [''] * len(timeslots)
tt3[0] = ''
tt3[1] = 'T3' 
tlh1 = [''] * len(timeslots) 
tlh1[0] = ''
tlh1[1] = 'LH1'
tlh2 = [''] * len(timeslots) 
tlh2[0] = ''
tlh2[1] = 'LH2'
tlab = [''] * len(timeslots) 
tlab[0] = ''
tlab[1] = 'LAB'
tground = [''] * len(timeslots) 
tground[0] = ''
tground[1] = 'ground'

for entry in Tuesday:
    course = entry[0]
    room = entry[1]
    time = entry[3]
    prof = entry[4]
    batch = entry[5]
    i = timeslots.index(time)
    if(room=='T1'):
        newTuesday[i] += ' ('+course+') '
    elif(room=='T2'):
        tt2[i] += ' ('+course+') '
    elif(room=='T3'):
        tt3[i] += ' ('+course+') '
    elif(room=='LH1'):
        tlh1[i] += ' ('+course+') '
    elif(room=='LH2'):
        tlh2[i] += ' ('+course+') '
    elif('LAB' in room or 'lab' in room or 'Lab' in room):
        tlab[i] += ' ('+course+','+room+') '
    elif(room=='ground'):
        tground[i] += ' ('+course+') '

wt2 = [''] * len(timeslots)
wt2[0] = ''
wt2[1] = 'T2' 
wt3 = [''] * len(timeslots)
wt3[0] = ''
wt3[1] = 'T3' 
wlh1 = [''] * len(timeslots) 
wlh1[0] = ''
wlh1[1] = 'LH1'
wlh2 = [''] * len(timeslots) 
wlh2[0] = ''
wlh2[1] = 'LH2'
wlab = [''] * len(timeslots) 
wlab[0] = ''
wlab[1] = 'LAB'
wground = [''] * len(timeslots) 
wground[0] = ''
wground[1] = 'ground'

for entry in Wednesday:
    course = entry[0]
    room = entry[1]
    time = entry[3]
    prof = entry[4]
    batch = entry[5]
    i = timeslots.index(time)
    if(room=='T1'):
        newWednesday[i] += ' ('+course+') '
    elif(room=='T2'):
        wt2[i] += ' ('+course+') '
    elif(room=='T3'):
        wt3[i] += ' ('+course+') '
    elif(room=='LH1'):
        wlh1[i] += ' ('+course+') '
    elif(room=='LH2'):
        wlh2[i] += ' ('+course+') '
    elif('LAB' in room or 'lab' in room or 'Lab' in room):
        wlab[i] += ' ('+course+','+room+') '
    elif(room=='ground'):
        wground[i] += ' ('+course+') '

tht2 = [''] * len(timeslots)
tht2[0] = ''
tht2[1] = 'T2' 
tht3 = [''] * len(timeslots)
tht3[0] = ''
tht3[1] = 'T3' 
thlh1 = [''] * len(timeslots) 
thlh1[0] = ''
thlh1[1] = 'LH1'
thlh2 = [''] * len(timeslots) 
thlh2[0] = ''
thlh2[1] = 'LH2'
thlab = [''] * len(timeslots) 
thlab[0] = ''
thlab[1] = 'LAB'
thground = [''] * len(timeslots) 
thground[0] = ''
thground[1] = 'ground'

for entry in Thursday:
    course = entry[0]
    room = entry[1]
    time = entry[3]
    prof = entry[4]
    batch = entry[5]
    i = timeslots.index(time)
    if(room=='T1'):
        newThursday[i] += ' ('+course+') '
    elif(room=='T2'):
        tht2[i] += ' ('+course+') '
    elif(room=='T3'):
        tht3[i] += ' ('+course+') '
    elif(room=='LH1'):
        thlh1[i] += ' ('+course+') '
    elif(room=='LH2'):
        thlh2[i] += ' ('+course+') '
    elif('LAB' in room or 'lab' in room or 'Lab' in room):
        thlab[i] += ' ('+course+','+room+') '
    elif(room=='ground'):
        thground[i] += ' ('+course+') '

ft2 = [''] * len(timeslots)
ft2[0] = ''
ft2[1] = 'T2' 
ft3 = [''] * len(timeslots)
ft3[0] = ''
ft3[1] = 'T3' 
flh1 = [''] * len(timeslots) 
flh1[0] = ''
flh1[1] = 'LH1'
flh2 = [''] * len(timeslots) 
flh2[0] = ''
flh2[1] = 'LH2'
flab = [''] * len(timeslots) 
flab[0] = ''
flab[1] = 'LAB'
fground = [''] * len(timeslots) 
fground[0] = ''
fground[1] = 'ground'

for entry in Friday:
    course = entry[0]
    room = entry[1]
    time = entry[3]
    prof = entry[4]
    batch = entry[5]
    i = timeslots.index(time)
    if(room=='T1'):
        newFriday[i] += ' ('+course+') '
    elif(room=='T2'):
        ft2[i] += ' ('+course+') '
    elif(room=='T3'):
        ft3[i] += ' ('+course+') '
    elif(room=='LH1'):
        flh1[i] += ' ('+course+') '
    elif(room=='LH2'):
        flh2[i] += ' ('+course+') '
    elif('LAB' in room or 'lab' in room or 'Lab' in room):
        flab[i] += ' ('+course+','+room+') '
    elif(room=='ground'):
        fground[i] += ' ('+course+') '

realprofcourse = list(realprofcourse)
realprofcourse.insert(0,'(Professor,course assigned)')
with open('timetable.csv', 'w') as csvfile: 
    # creating a csv writer object 
    csvwriter = csv.writer(csvfile) 
    # writing the fields 
    csvwriter.writerow(timeslots)
    csvwriter.writerow(newMonday)
    csvwriter.writerow(mt2)
    csvwriter.writerow(mt3)
    csvwriter.writerow(mlh1)
    csvwriter.writerow(mlh2)
    csvwriter.writerow(mlab)
    csvwriter.writerow(mground)    
    csvwriter.writerow(newTuesday)   
    csvwriter.writerow(tt2)
    csvwriter.writerow(tt3)
    csvwriter.writerow(tlh1)
    csvwriter.writerow(tlh2)
    csvwriter.writerow(tlab) 
    csvwriter.writerow(tground)  
    csvwriter.writerow(newWednesday)  
    csvwriter.writerow(wt2)
    csvwriter.writerow(wt3)
    csvwriter.writerow(wlh1)
    csvwriter.writerow(wlh2)
    csvwriter.writerow(wlab) 
    csvwriter.writerow(wground)   
    csvwriter.writerow(newThursday)   
    csvwriter.writerow(tht2)
    csvwriter.writerow(tht3)
    csvwriter.writerow(thlh1)
    csvwriter.writerow(thlh2)
    csvwriter.writerow(thlab) 
    csvwriter.writerow(thground)  
    csvwriter.writerow(newFriday)
    csvwriter.writerow(ft2)
    csvwriter.writerow(ft3)
    csvwriter.writerow(flh1)
    csvwriter.writerow(flh2)
    csvwriter.writerow(flab)
    csvwriter.writerow(fground)
    csvwriter.writerow(realprofcourse)
print 'Timetable created in an excel by the name "timetable.csv" in the same folder'