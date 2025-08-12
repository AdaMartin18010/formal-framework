# 教育架构DSL草案

## 1. 概述

教育架构DSL用于统一描述教育信息化系统：学生信息、课程教务、在线学习、测评考试、出勤、学习分析等，支持与SIS、LMS、EMS对接。

## 2. 核心语法定义

### 2.1 学生与学籍管理

```yaml
student_management:
  students:
    - id: "stu_0001"
      name: "Alice"
      grade: 10
      clazz: "10-2"
      enrollment_date: "2024-09-01"
      status: "active"
      guardians:
        - name: "Parent A"
          phone: "123456"
          email: "parent@example.com"
          relationship: "mother"
      accommodations: ["extra_time", "quiet_room"]
      special_needs: ["dyslexia"]
  academic_records:
    - student: "stu_0001"
      year: 2024
      semester: "fall"
      gpa: 3.8
      credits_earned: 24
      honors: ["dean_list"]
```

### 2.2 教师与员工管理

```yaml
faculty_management:
  teachers:
    - id: "T_001"
      name: "Dr. Smith"
      department: "Mathematics"
      subjects: ["Algebra", "Calculus"]
      qualifications: ["PhD", "Teaching_Cert"]
      availability:
        - day: "Mon"; slots: [1, 2, 3, 4]
        - day: "Wed"; slots: [1, 2, 5, 6]
  staff:
    - id: "S_001"
      name: "Ms. Johnson"
      role: "counselor"
      department: "Student_Services"
      caseload: 150
```

### 2.3 课程与排课系统

```yaml
curriculum_scheduling:
  courses:
    - code: "MATH101"
      name: "Algebra"
      credit: 4
      prerequisites: []
      corequisites: []
      department: "Mathematics"
      difficulty: "intermediate"
      max_enrollment: 30
      description: "Introduction to algebraic concepts"
  timetable:
    - clazz: "10-2"
      entries:
        - day: "Mon"
          slot: 1
          room: "A101"
          course: "MATH101"
          teacher: "T_001"
          capacity: 30
        - day: "Tue"
          slot: 3
          room: "C201"
          course: "CS102"
          teacher: "T_009"
          capacity: 25
  room_management:
    - room: "A101"
      capacity: 35
      equipment: ["projector", "whiteboard", "computers"]
      building: "Science"
      floor: 1
```

### 2.4 在线学习与资源管理

```yaml
learning_management:
  lms_platform:
    name: "Canvas"
    version: "2024.1"
    features: ["discussions", "assignments", "quizzes", "gradebook"]
  resources:
    - id: "res_001"
      type: "video"
      title: "Sorting Algorithms"
      duration_min: 20
      format: "mp4"
      size_mb: 150
      tags: ["algorithms", "computer_science"]
    - id: "res_002"
      type: "pdf"
      title: "Algebra Notes"
      pages: 45
      format: "pdf"
      size_mb: 2.5
      tags: ["mathematics", "algebra"]
  activities:
    - id: "act_001"
      type: "quiz"
      course: "CS102"
      title: "Sorting Quiz"
      open_date: "2025-03-01"
      due_date: "2025-03-08"
      time_limit_min: 30
      attempts_allowed: 2
      questions:
        - type: "multiple_choice"
          points: 5
          text: "What is the time complexity of bubble sort?"
          options: ["O(n)", "O(n²)", "O(log n)", "O(n log n)"]
          correct: 1
```

### 2.5 测评考试系统

```yaml
assessment_system:
  exam_types:
    - name: "midterm"
      weight: 0.3
      duration_min: 90
      format: "paper"
    - name: "final"
      weight: 0.4
      duration_min: 120
      format: "paper"
    - name: "quiz"
      weight: 0.1
      duration_min: 20
      format: "online"
  exams:
    - id: "exam_mid_1"
      course: "MATH101"
      type: "midterm"
      date: "2025-03-15"
      start_time: "09:00"
      duration_min: 90
      rooms: ["A101", "A102"]
      proctors: ["T_001", "T_002"]
  grading:
    scale: ["A", "B", "C", "D", "F"]
    grade_points: {"A": 4.0, "B": 3.0, "C": 2.0, "D": 1.0, "F": 0.0}
    rules:
      - name: "curve"
        method: "gaussian_curve"
        mean: 75
        std: 10
      - name: "participation"
        weight: 0.1
        criteria: ["attendance", "discussion", "homework"]
```

### 2.6 出勤与纪律管理

```yaml
attendance_discipline:
  attendance_rules:
    - late_threshold_min: 10
    - absence_threshold_pct: 30
    - tardy_penalty: 0.5
    - excused_absence_types: ["medical", "family_emergency", "religious"]
  attendance_records:
    - student: "stu_0001"
      date: "2025-03-02"
      status: "present"
      time_in: "08:45"
      time_out: "15:30"
      notes: ""
  discipline:
    incidents:
      - student: "stu_0002"
        date: "2025-03-01"
        type: "tardiness"
        severity: "minor"
        action: "warning"
        description: "Late to class by 15 minutes"
    policies:
      - level: "minor"
        actions: ["warning", "detention"]
      - level: "major"
        actions: ["suspension", "parent_conference"]
```

### 2.7 学习分析与预测

```yaml
learning_analytics:
  data_sources:
    - name: "lms_activity"
      frequency: "daily"
      metrics: ["login_time", "resource_access", "assignment_submission"]
    - name: "assessment_scores"
      frequency: "weekly"
      metrics: ["quiz_scores", "assignment_grades", "exam_results"]
    - name: "attendance_data"
      frequency: "daily"
      metrics: ["attendance_rate", "tardiness", "participation"]
  features:
    - name: "engagement"
      calculation: "weighted_average(login_frequency, resource_access, participation)"
    - name: "progress"
      calculation: "grade_trend_over_time"
    - name: "risk"
      calculation: "dropout_probability_model"
  models:
    - name: "dropout_risk"
      type: "classification"
      algorithm: "xgboost"
      features: ["gpa", "attendance", "engagement", "socioeconomic_status"]
      target: "dropout_indicator"
      update_frequency: "weekly"
    - name: "grade_prediction"
      type: "regression"
      algorithm: "random_forest"
      features: ["previous_grades", "attendance", "homework_completion"]
      target: "final_grade"
  alerts:
    - name: "high_risk_student"
      condition: "dropout_risk > 0.7"
      action: ["notify_counselor", "schedule_intervention"]
    - name: "grade_decline"
      condition: "grade_trend < -0.5"
      action: ["notify_teacher", "schedule_tutoring"]
```

### 2.8 财务与收费管理

```yaml
financial_management:
  tuition:
    - grade: 10
      annual_tuition: 15000
      payment_plans: ["full", "semester", "monthly"]
      discounts:
        - type: "sibling"
          amount: 0.1
        - type: "early_payment"
          amount: 0.05
  fees:
    - name: "technology_fee"
      amount: 500
      frequency: "annual"
      description: "Laptop and software access"
    - name: "activity_fee"
      amount: 200
      frequency: "annual"
      description: "Extracurricular activities"
  billing:
    - student: "stu_0001"
      academic_year: "2024-2025"
      total_charges: 15700
      payments_received: 8000
      balance: 7700
      due_date: "2025-01-15"
```

## 3. 高级特性

```yaml
advanced_features:
  integration:
    sis_systems: ["PowerSchool", "Blackbaud", "Skyward"]
    lms_platforms: ["Canvas", "Moodle", "Blackboard"]
    communication_tools: ["Remind", "ClassDojo", "Seesaw"]
  automation:
    grade_calculation: true
    attendance_tracking: true
    report_generation: true
    parent_notifications: true
  analytics:
    real_time_dashboard: true
    predictive_modeling: true
    intervention_tracking: true
    outcome_measurement: true
```

## 4. 自动化生成示例

```python
# 基于成绩与参与度的风险预警
def calculate_risk_score(student_data):
    grade_factor = 0.6 * (100 - student_data['gpa'] * 25) / 100
    engagement_factor = 0.4 * (1 - student_data['engagement_score'])
    attendance_factor = 0.2 * (1 - student_data['attendance_rate'])
    return grade_factor + engagement_factor + attendance_factor

# 自动排课算法
def generate_timetable(courses, teachers, rooms, constraints):
    from ortools.sat.python import cp_model
    
    model = cp_model.CpModel()
    # 创建变量
    assignments = {}
    for course in courses:
        for teacher in teachers:
            for room in rooms:
                for day in range(5):
                    for slot in range(8):
                        assignments[(course, teacher, room, day, slot)] = model.NewBoolVar(f'{course}_{teacher}_{room}_{day}_{slot}')
    
    # 添加约束条件
    # 1. 每个课程只能安排一次
    for course in courses:
        model.Add(sum(assignments[(course, t, r, d, s)] for t in teachers for r in rooms for d in range(5) for s in range(8)) == 1)
    
    # 2. 每个时间段每个房间只能安排一个课程
    for room in rooms:
        for day in range(5):
            for slot in range(8):
                model.Add(sum(assignments[(c, t, room, day, slot)] for c in courses for t in teachers) <= 1)
    
    # 3. 教师时间冲突检查
    for teacher in teachers:
        for day in range(5):
            for slot in range(8):
                model.Add(sum(assignments[(c, teacher, r, day, slot)] for c in courses for r in rooms) <= 1)
    
    solver = cp_model.CpSolver()
    status = solver.Solve(model)
    
    if status == cp_model.OPTIMAL:
        return extract_schedule(assignments, solver)
    else:
        return None

# 学习路径推荐
def recommend_learning_path(student_profile, academic_goals):
    current_level = assess_current_level(student_profile)
    target_level = academic_goals['target_level']
    
    path = []
    while current_level < target_level:
        next_courses = get_recommended_courses(current_level, student_profile['interests'])
        path.extend(next_courses)
        current_level += 1
    
    return {
        'path': path,
        'estimated_duration': len(path) * 4,  # 假设每门课4个月
        'prerequisites': get_prerequisites(path),
        'resources': get_learning_resources(path)
    }
```

## 5. 验证与测试

```python
class EducationDSLValidator:
    def validate_student_data(self, student):
        assert 'id' in student, "Student must have ID"
        assert 'name' in student, "Student must have name"
        assert 'grade' in student and 1 <= student['grade'] <= 12, "Grade must be between 1-12"
        assert 'status' in student and student['status'] in ['active', 'inactive', 'graduated'], "Invalid status"
    
    def validate_timetable(self, timetable):
        for entry in timetable['entries']:
            assert entry['slot'] in range(1, 9), "Slot must be between 1-8"
            assert entry['day'] in ['Mon', 'Tue', 'Wed', 'Thu', 'Fri'], "Invalid day"
            assert 'room' in entry, "Entry must specify room"
            assert 'course' in entry, "Entry must specify course"
            assert 'teacher' in entry, "Entry must specify teacher"
    
    def validate_grading_scale(self, scale):
        valid_grades = ['A', 'B', 'C', 'D', 'F']
        assert all(grade in valid_grades for grade in scale), "Invalid grade in scale"
    
    def validate_attendance_rules(self, rules):
        assert rules['late_threshold_min'] > 0, "Late threshold must be positive"
        assert 0 <= rules['absence_threshold_pct'] <= 100, "Absence threshold must be 0-100%"
    
    def validate_learning_analytics(self, analytics):
        assert 'features' in analytics, "Analytics must define features"
        assert 'models' in analytics, "Analytics must define models"
        for model in analytics['models']:
            assert 'algorithm' in model, "Model must specify algorithm"
            assert 'features' in model, "Model must specify features"
```

## 6. 总结

本DSL覆盖教育领域的核心业务要素，包括学生管理、课程排课、在线学习、测评考试、出勤管理、学习分析等，可用于自动生成SIS/LMS配置、排课表、考试规则与学习分析参数，支持教育信息化的全面数字化转型。
